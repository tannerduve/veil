# Invariant Synthesis

`#synthesize_invariants` looks for `invariant` clauses that make a module's
`safety` properties inductive. It finds them, finds an execution that violates
the properties, or reports that no universal strengthening exists. With
`certify`, an invariant or a violation becomes a theorem checked by the Lean
kernel.

- [Usage](#usage)
- [Outcomes](#outcomes)
- [Algorithm](#algorithm)
- [What `certify` guarantees](#what-certify-guarantees)
- [Semantics](#semantics)
- [Existential invariants](#existential-invariants)
- [Results on Veil's examples](#results-on-veils-examples)
- [Limitations](#limitations)

## Usage

The command is not part of `import Veil`. Import
`Veil.Core.Tools.Synthesizer` and run the command after `#gen_spec`:

```lean
module

public import Veil
public import Veil.Core.Tools.Synthesizer

veil module LockServer

type client

relation waiting : client → Bool
relation holds : client → Bool
individual lock_free : Bool

#gen_state

after_init {
  waiting C := false
  holds C := false
  lock_free := true
}

action request (c : client) {
  waiting c := true
}

action grant (c : client) {
  require lock_free
  require waiting c
  waiting c := false
  holds c := true
  lock_free := false
}

action release (c : client) {
  require holds c
  holds c := false
  lock_free := true
}

safety [mutex] holds C ∧ holds D → C = D

#gen_spec

#synthesize_invariants certify

end LockServer
```

The command prints the strengthening as lines to paste into the module, and
`certify` adds the theorem `LockServer.ic3_safe`:

```
Inductive invariant found at frame 1 with 1 strengthening clause(s) (…):
invariant [ic3_0] ∀ (x0 : client), ¬ holds x0 ∨ ¬ lock_free
Certified: theorem LockServer.ic3_safe (strengthening LockServer.ic3_inv); axioms: #[propext, Classical.choice, Quot.sound]; kernel-checked, standard axioms only
```

`Examples/Ivy/RicartAgrawalaSynthesis.lean`,
`Examples/TLA/TwoPhaseCommitSynthesis.lean` and
`Examples/Puzzles/RiverCrossingSynthesis.lean` run the command on three of
Veil's examples.

### Options

Options may appear in any order, each at most once:
`#synthesize_invariants (fuel := 500) (log := "run.jsonl") verbose certify`.

| option | meaning | default |
|---|---|---|
| `(fuel := n)` | Maximum number of solver calls. | 5000 |
| `(invariants := true)` | Include the module's declared `invariant`s in the property. | `false` |
| `(generalizer := g)` | `linear` first tries linear relations between integer individuals (`x + y = z`, `x ≤ y + c`, …), then the paper's generalizer; `updr` uses the paper's alone. They agree on a module without integer state. | `linear` |
| `(cores := false)` | Generalize from the full negated diagram, as the paper does, instead of the solver's unsat cores. | `true` |
| `(log := "path.jsonl")` | Append one JSON object per event (each candidate clause and its verdict, each clause admitted, each frame cleared, the outcome) to this file. | no log |
| `(expect := v)` | The expected outcome: `invariant`, `unsafe`, `no_universal_invariant` or `unknown`. It is reported as information, any other outcome as an error. For tests. | none |
| `verbose` | Report each step of the search. | off |
| `certify` | Prove the outcome as a theorem checked by the kernel. | off |

Lean options:

| option | meaning | default |
|---|---|---|
| `veil.synthesizer.trust` | Let the search take the solver's `unsat` answers on faith instead of reconstructing proofs. Certificates always reconstruct. | `false` |
| `veil.synthesizer.normalizeTr` | Write the queries with the transition relation normalized once per module (`Mod.ic3_trNorm`, equal to Veil's `tr` by the kernel-checked `Mod.ic3_tr_eq_norm`). With `false`, every query pays Veil's preprocessing of the actions. | `true` |
| `veil.synthesizer.timings` | Report the wall time of the search and of the certificate. | `false` |
| `veil.smt.timeout` | The solver timeout. A query the search cannot do without is asked again with twice the timeout before the search stops. | 60 s |
| `trace.veil.synthesizer.debug` | Diagnostic traces. | `false` |

## Outcomes

| outcome | `expect` value | what is printed | with `certify` |
|---|---|---|---|
| Inductive invariant | `invariant` | The strengthening as `invariant [ic3_k] …` lines, none when the property is inductive on its own. | `Mod.ic3_safe : ∀ th st, reachable th st → ic3_prop th st`, with the predicates `ic3_inv` (the property and the strengthening) and `ic3_prop` (the property), and one initiation and one consecution theorem per conjunct of `ic3_inv`. |
| Violation | `unsafe` | An execution from an initial state to a state violating the property, and a `sat trace` block that re-checks it with Veil's bounded model checker. An error unless expected. | `Mod.ic3_unsafe`: at the model's sort sizes and typeclass instances, not every reachable state satisfies `ic3_prop`. |
| No universal inductive invariant | `no_universal_invariant` | An abstract counterexample: finite structures, the first contained in an initial state, each next contained in a successor of a state containing the previous, and a successor of the last violating the property. | Nothing: the verdict is not a theorem. |
| Stopped | `unknown` | Why the search stopped (fuel, a solver timeout, a query that could not be posed) and the clauses per frame. | Nothing. |

A module holds one certificate, since the theorem names are fixed. A run that
asks about transitions also adds `Mod.ic3_trNorm` and `Mod.ic3_tr_eq_norm`, and
later runs in the module reuse them.

## Algorithm

The search is UPDR, the first-order form of IC3/PDR, from Aleksandr Karbyshev,
Nikolaj Bjørner, Shachar Itzhaky, Noam Rinetzky and Sharon Shoham,
"Property-Directed Inference of Universal Invariants or Proving Their
Absence", *Journal of the ACM* 64(1), 2017.

The search keeps *frames* `F₁ … F_N`: sets of universal clauses
`∀ x̄, l₁ ∨ … ∨ lₙ` over the module's relations, functions, individuals, enum
constructors and typeclass symbols. `F_i` over-approximates the states
reachable in at most `i` steps, and every frame contains the property.

1. Ask for a state of `F_N` with a successor that violates the property. If
   there is none, push each clause of `F_i` preserved from `F_i` into
   `F_{i+1}`. Two equal frames are an inductive invariant; otherwise open
   `F_{N+1}` and repeat.
2. A state found in step 1 is a finite structure. Its *diagram* is the
   existential formula true of every state containing a copy of it, so the
   negated diagram is a universal clause that excludes them all. To exclude
   the structure from `F_j`, ask for a predecessor in `F_{j-1}`, and exclude a
   predecessor from `F_{j-1}` first.
3. Without a predecessor, *generalize* the negated diagram: drop literals while
   the clause still holds initially and is preserved from `F_{j-1}`. The search
   starts from the literals the solver's unsat cores name, then drops the rest
   in groups, from the most specific (values, equalities) to the most
   structural (the module's own relations). A candidate costs two solver calls,
   unless a state known to be reachable already refutes it.
4. When a chain of predecessors reaches the initial states, one bounded query
   asks whether a real execution of that length violates the property. If one
   does, it is the counterexample. If none does, no universal inductive
   invariant over the module's vocabulary proves the property (Proposition 5.6
   of the paper).

Every question is posed through Veil's own tactic pipeline and cvc5, as
`#check_invariants` and `sat trace` pose theirs.

## What `certify` guarantees

`certify` does not take the search at its word. It builds the theorem from
fresh solver answers, and the kernel checks it.

- **Invariant.** Each conjunct of `ic3_inv` has two obligations: it holds
  initially, and every action preserves it from a state satisfying `ic3_inv`.
  Both are asked again, lean-smt replays each answer as a Lean proof, and the
  kernel checks it. `ic3_safe` applies
  `RelationalTransitionSystem.invariant_of_inductive` and `Invariant.mono`
  (`Veil/Core/Tools/Synthesizer/Soundness.lean`) to these theorems.
- **Violation.** Each fact of the execution is proven by evaluation on the
  concrete states, at `Fin n` for each sort, and `ic3_unsafe` applies
  `RelationalTransitionSystem.not_invariant_of_reachable`. Nothing rests on
  the solver.
- `#print axioms` lists `propext`, `Classical.choice` and `Quot.sound` only,
  and the command reports "kernel-checked, standard axioms only". A solver step
  that lean-smt cannot replay, or whose replay the kernel rejects, is taken on
  the solver's word: a warning names it, its theorem is named
  `ic3_init_i_trusted` or `ic3_cons_i_trusted`, and the certificate then
  depends on `sorryAx`, which the command reports.
- A bug in the search can make a certificate fail. It cannot make a false
  theorem.
- The no-universal-invariant verdict is not certified. It rests on the search
  and on Proposition 5.6 of the paper, which is not formalized here. The paper
  states it for constants and relations. For function symbols and enum sorts
  the verdict rests on an extension of its argument (a universal sentence
  passes to a substructure closed under the functions, and an enum carrier is
  fixed), and the message says so.

## Semantics

Every verdict is about Veil's `relationalTransitionSystem`:

- its initial states run `after_init` from the default state, so a field that
  `after_init` never assigns keeps its default value;
- its transitions are the module's actions under the module's `assumption`s;
- `trusted invariant`s are neither assumed nor checked.

`#check_invariants` differs in two ways. It assumes trusted invariants, so a
counterexample found here can pass through states a trusted invariant
excludes; the message says so. It proves initiation from an arbitrary
pre-state, so a clause certified here can fail its initiation check when
`after_init` leaves a field unassigned; the command warns about such fields.

## Existential invariants

The search finds universal clauses only. For a property that needs an
existential:

- With `(invariants := true)` the declared invariants, existentials included,
  are part of the property. When they are inductive together with the safety
  property, the command finds no further clause and the certificate replays
  the author's proof.
- A ghost function that names the witness (`quorumOf : node → quorum`,
  maintained by the action that elects the leader) turns an existential fact
  into a universal clause over that function.

## Results on Veil's examples

Each example was run from Veil's `Examples/` at commit 02791b2d with its
safety property only: a property stated as an `invariant` was restated as
`safety`, and every other invariant and every command after `#gen_spec` was
dropped. Each run ends with `#synthesize_invariants certify`.

| Example | Source | Result | Solver calls | Search time |
|---|---|---|---|---|
| DecentralizedLock | Ivy | property inductive on its own, certified | 3 | 6 s |
| RicartAgrawala | Ivy | invariant, 2 clauses, certified | 142 | 140 s |
| TwoPhaseCommit | Ivy | invariant, 9 clauses, certified | 345 | 317 s |
| TwoPhaseCommit | TLA | invariant, 12 clauses, certified | 496 | 478 s |
| Ring | Ivy | invariant, 18 clauses, certified | 1,920 | 2,165 s |
| Peterson | TLA | invariant, 23 clauses; certificate not reached within a 40 min cap | 1,758 | 2,239 s |
| RiverCrossing | Puzzles | counterexample, 7 steps, certified | 297 | 49 s |
| DieHard | Puzzles | counterexample, 6 steps, certified | 223 | 51 s |
| Traffic | TLA | counterexample, 2 steps, certified | 23 | 9 s |
| Bakery, EWD840, BuggyCircularBuffer | TLA | refused: index of type `Fin n` | | |
| MutexViolation | TLA | refused: queue-valued individual | | |
| Room | TLA | refused: structure-valued function | | |
| SimpleAllocator | TLA | refused: set-valued field | | |

- **Every example in the supported fragment got an answer, and no answer was
  wrong.** Every certificate was kernel-checked on the standard axioms alone.
- **The invariants are correct but larger than the hand-written ones.**
  RicartAgrawala's two clauses match Veil's two hand-written invariants; Ring
  needs 18 clauses where Veil has 3, and Peterson 23 where Veil has 4. UPDR
  learns many narrow clauses where a person writes a few general ones.
- **The counterexamples are the puzzles' solutions.** DieHard's ends with 4
  litres in the big jug.
- **Traffic exercises two corner cases.** Its action `Cycle` shares its name
  with an enum constructor, and its counterexample's steps rewrite one row of a
  relation over two enums.
- The exact clauses and call counts depend on the models cvc5 returns, which
  vary with incidental state such as the names of bound variables.

## Limitations

- **A fragment of Veil.** The command handles:
  - uninterpreted sorts, enums and `Bool`;
  - relations, functions and individuals over sorts;
  - `Int`/`Nat` as values (not as arguments), with linear templates for
    counters;
  - theories given as typeclass instances with axioms, such as a total order.

  It refuses anything else at startup, with a message naming the component:
  `Fin n` indices, queues, sets, structures, child modules, and classes that
  extend other classes. It never searches over a partial vocabulary. Veil's
  Ivy-style examples are written in this fragment; most of its TLA examples
  use concrete data types for model checking and are not.
- **Universal clauses only.** A property whose proof needs an existential, or
  arithmetic over a quantified index, has no invariant of the form
  `∀ x…, l₁ ∨ … ∨ lₙ`.
- **"No universal invariant" is a diagnosis, not a proof.** Only `ic3_safe`
  and `ic3_unsafe` are theorems. A run can also end without an answer: out of
  fuel, a solver timeout, or a query the command cannot pose. None of these is
  reported as safe or unsafe.
- **Speed.** Small models take seconds to minutes; Ring and Peterson take about
  35 minutes, measured next to other builds. Most of the time goes to
  preparing queries: Ring spent 1,375 s in Veil's and lean-smt's preprocessing
  and 641 s in the solver.
- **Counterexample certificates evaluate.** A step that evaluation and the enum
  case split cannot prove is reported as a violation without a theorem.
