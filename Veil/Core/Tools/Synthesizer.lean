module

public import Veil
public import Veil.Core.Tools.Synthesizer.Soundness
public meta import Veil.Core.Tools.Synthesizer.Command

/-! # Invariant synthesis

`#synthesize_invariants`, run after `#gen_spec` inside a Veil module, either
finds universal `invariant` clauses that make the module's `safety` properties
inductive, or finds an execution that violates them. With `certify`, either
answer becomes a kernel-checked theorem in the module's namespace: `ic3_safe`
or `ic3_unsafe`.

The search is UPDR, the first-order form of IC3, from Karbyshev, Bjørner,
Itzhaky, Rinetzky and Shoham, "Property-Directed Inference of Universal
Invariants or Proving Their Absence", JACM 2017. See
`docs/InvariantSynthesis.md` for usage, options and limitations.

The command is not part of `import Veil`; import this module to use it:

```lean
module

public import Veil
public import Veil.Core.Tools.Synthesizer
```

The modules, in dependency order:

* `Clause`: universal clauses and finite structures as data; diagrams and
  subsumption.
* `Linear`: candidate linear relations between integer individuals.
* `Render`: clauses as Veil terms and as text.
* `Vocabulary`: the module's symbols, and solver models read as finite
  structures.
* `Query`: the solver queries, posed through Veil's tactic pipeline, and the
  normalized transition relation.
* `Controller`: the UPDR loop.
* `Soundness`: the reachability lemmas the certificates use.
* `Certificate`: the safety theorem `ic3_safe`.
* `Counterexample`: the refutation theorem `ic3_unsafe`.
* `Command`: the `#synthesize_invariants` command.
-/
