module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Clause
public meta import Veil.Core.Tools.Synthesizer.Render
public meta import Veil.Core.Tools.Synthesizer.Vocabulary
public meta import Veil.Core.Tools.Synthesizer.Query
public meta import Veil.Core.Tools.Synthesizer.Linear

/-!
# The UPDR controller

Universal property-directed reachability (Karbyshev et al., JACM 2017), in the
proof-obligation formulation of PDR. Two terms are used throughout:

* An *obligation* `(j, σ)` is a finite structure `σ` that frame `j` must
  exclude: some state containing `σ` as a substructure is `N - j + 1` steps
  from a state violating the property, so `F_j` may not contain such a state.
* A clause `c` is *inductive relative to* a frame `F` when `F ∧ tr ⇒ c'`: every
  transition from a state satisfying `F` (and the property) lands in a state
  satisfying `c`.

The algorithm:

* Frames `F₁ … F_N`, each a set of universal clauses; every frame implicitly
  includes the property `P`; `F₀` is `init` and is never materialized. Frames
  are ordered by implication, `F_i ⇒ F_{i+1}`, not by inclusion of clause
  sets: a push may replace a weaker clause of `F_{i+1}` by a stronger one that
  `F_{i+2}` does not hold.
* While the frontier `F_N` has a state one step from `¬P`, put `(N, σ)` on the
  obligation stack. The frontier is asked one property conjunct at a time
  (`frontierQuery`), as are the two initial checks. To discharge `(j, σ)`: ask for a predecessor of `Diag(σ)`
  (the diagram of `σ`: the existential sentence true in exactly the states
  containing `σ` as a substructure, `Clause.lean`) in `F_{j-1}`. A
  predecessor `σ'` becomes the obligation `(j-1, σ')`. When
  there is none and `init ∧ Diag(σ)` is satisfiable, the abstract
  counterexample reaches the initial states (see below); otherwise `¬Diag(σ)`
  is generalized and added to `F₁ … F_j`. An obligation at level 0 came out of
  a predecessor query against `init`, so its structure is contained in an
  initial state by construction and no query is needed (Section 4.3).
* When the frontier is clear, open `F_{N+1}` and, for every `i ≤ N`, push each
  clause of `F_i` that is inductive relative to `F_i` into `F_{i+1}`. Equal
  consecutive frames are a fixpoint: that frame's clauses, with `P`, form an
  inductive invariant.
* An abstract counterexample whose newest structure (the one at the lowest
  level, first in the reported chain and closest to the initial states) meets
  `init` means no universal inductive invariant exists
  for this property (Prop. 5.6). When it is rooted at level 0 it describes a
  concrete path of `N + 1` steps, and a bounded path query tells whether that
  path is real (`analyzeCEX`).

A solver answer of `unknown` (a timeout, most often) to a query whose verdict
the search cannot do without (the frontier, the two initial checks, an
obligation's predecessor and initiation queries, the bounded path check) is
asked once more with twice `veil.smt.timeout` before the search stops
(`SearchM.solveCore`); generalization, propagation and reuse treat an unknown
answer as a missing one and move on.

Every clause enters a frame only after two solver calls said `unsat`:
`init ∧ ¬c` (initiation) and `F_{j-1} ∧ tr ∧ Diag_L'` (no predecessor),
where `Diag_L` is the generalized diagram. The controller keeps only the
clauses and whether any verdict came from a trusted solver. For the invariant
and counterexample verdicts its result is not taken at its word:
`Certificate.lean` and `Counterexample.lean` re-check it and build the theorem
from fresh facts, so a bug here can make a certificate fail to build but
cannot make a theorem false. The no-universal-invariant verdict is different:
it is this code's own answer, and its soundness argument uses Proposition 5.6
of the paper, a theorem not yet formalized in Lean. For that verdict this
code is part of what must be trusted.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Term Meta Veil

/-- A clause admitted into a frame. `viaTrust` says whether one of its two
admission queries was answered by a trusted solver (no reconstructed proof).
It is informational: the uncertified message reports it, and `certify` re-runs
every query. -/
structure Admitted where
  clause : Clause
  term : Term
  viaTrust : Bool

/-- Which generalizer proposes the clause that blocks a counterexample. Every
proposal is checked for initiation and consecution before it is admitted, so
the choice affects the clauses found and the time taken, not soundness. -/
inductive GeneralizerKind where
  /-- The paper's: unsat cores, then literal deletion from the negated diagram. -/
  | updr
  /-- Linear templates over the integer individuals first (`Linear.lean`),
  then `updr`. The same as `updr` on a module without integers. -/
  | linear
deriving BEq, Repr, Inhabited

structure Config where
  /-- Maximum number of solver calls before giving up. -/
  fuel : Nat := 5000
  generalizer : GeneralizerKind := .linear
  /-- Linear template candidates tried per counterexample, two solver calls each. -/
  maxLinear : Nat := 24
  /-- Start generalization from the solver's unsat cores (the fast path). With
  `false`, generalization is the paper's: literals of the full negated diagram
  are dropped one at a time, cheapest first (`literalRank`), each deletion kept
  when the clause stays admissible. Slower, but a core that happens to name the
  successor and minimum facts of an ordered sort (`x is the k-th successor of
  zero`) cannot then hide the order facts (`le`) that generalize. -/
  cores : Bool := true
  /-- Length of the longest bounded path from `init` sampled before the search
  for the linear templates' reachable samples (one solver call per length). -/
  sampleDepth : Nat := 3
  /-- Maximum number of frames. -/
  maxFrames : Nat := 40
  /-- Try to drop literals from a blocking clause (UPDR generalization). -/
  generalize : Bool := true
  /-- Treat the module's declared `invariant`s as part of the property `P`.
  Off by default: a false declared invariant would otherwise be reported as a
  violation of the safety property. -/
  useDeclaredInvariants : Bool := false
  verbose : Bool := false
  /-- Append one JSON object per event (candidate clauses and their verdicts,
  clauses admitted or reused, frames opened) to this file as it happens. -/
  logFile : Option System.FilePath := none

/-- Counts kept across a run. -/
structure RunStats where
  /-- Solver calls made, reuse, generalization, propagation and bounded checks included. -/
  solverCalls : Nat := 0
  /-- Wall-clock milliseconds spent in those calls, every phase included. -/
  solverMs : Nat := 0
  /-- Wall-clock milliseconds of the calls by phase (statement elaboration,
  Veil's preprocessing, the `smt` tactic, model decoding), and the
  once-per-module normalization of the transition relation, which is outside
  the calls. -/
  phases : QueryPhases := {}
deriving Repr, Inhabited

/-- What the bounded path check said about an abstract counterexample that
reached the initial states (`analyzeCEX`). -/
inductive BoundedCheck where
  /-- Not asked: the chain is rooted above level 0, so it describes no
  execution of the frames' length. -/
  | notAsked
  /-- No execution of `steps` transitions violates the property. -/
  | noPath (steps : Nat)
  /-- The solver gave no answer about executions of `steps` transitions, so
  a real one may exist. -/
  | noAnswer (steps : Nat) (reason : String)

/-- The reason the log's `outcome` event carries for `Outcome.absenceWithheld`. -/
def absenceWithheldReason : String :=
  "the search closed without an invariant; the no-universal-invariant verdict is established only for vocabularies without integers (Proposition 5.6 of the paper is about uninterpreted sorts)"

inductive Outcome where
  /-- `clauses ∧ P` is an inductive invariant implying `P`. `anyTrusted` says
  whether any `unsat` verdict of the run came from a trusted solver. -/
  | foundInvariant (frame : Nat) (clauses : Array Admitted) (anyTrusted : Bool)
  /-- A concrete execution from `init` to a `¬P` state (`states`, `labels`). -/
  | «unsafe» (path : DecodedTrace)
  /-- A query whose `sat` answer is a violation of `P` (`init ∧ ¬P`,
  `init ∧ tr ∧ ¬P'`, or the bounded path check) answered `sat`, but its model
  could not be decoded (`reason`): `P` fails after `steps` transitions, and
  the execution cannot be shown or certified. -/
  | unsafeUndecoded (steps : Nat) (reason : String)
  /-- The abstract counterexample that no universal clause can cut, ordered
  from the structure contained in an initial state to the one whose successor
  violates `P`: no universal inductive invariant proves `P`. `check` is what
  the bounded path check said; with no answer from it, a real execution of
  that length may violate `P`. -/
  | noUniversalInvariant (diagrams : Array FinStructure) (check : BoundedCheck)
  /-- The search closed on an abstract counterexample (`diagrams`, ordered as
  in `noUniversalInvariant`) in a module with integer state, where
  Proposition 5.6 is not applied, so no verdict is given; reported as a
  stopped run. `check` is what the bounded path check said. `frameSizes`
  counts the strengthening clauses of `F₁ … F_N`. -/
  | absenceWithheld (diagrams : Array FinStructure) (check : BoundedCheck) (frameSizes : Array Nat)
  /-- The search stopped without a verdict: fuel, the frame limit, a solver
  answer of unknown or error, or a query that overran the per-query heartbeat
  budget. `frameSizes` counts the strengthening clauses of `F₁ … F_N`. -/
  | unknown (reason : String) (frameSizes : Array Nat)
  /-- The controller threw an exception: a bug in this code or in decoding a
  model, not a solver limit. -/
  | internalError (message : String) (frameSizes : Array Nat)

/-- What `synthesize` returns. -/
structure RunResult where
  outcome : Outcome
  stats : RunStats
  /-- The progress lines of the run, in order. -/
  log : Array String

/-- Read-only data of a run. -/
structure Ctx where
  cfg : Config
  qctx : QueryCtx
  sig : Signature
  /-- Terms of the property's conjuncts (`safety` and, optionally, `invariant`). -/
  property : Array Term
  /-- Each conjunct of `property` with its capitals quantified (`uqc%`). -/
  propertyConjuncts : Array Term
  /-- The conjunction of `propertyConjuncts`. -/
  propertyTerm : Term

/-- Mutable state of a run. -/
structure St where
  /-- `frames[i]` is `F_{i+1}`; `F₀ = init` is implicit. -/
  frames : Array (Array Admitted) := #[#[]]
  /-- Solver calls left. -/
  fuel : Nat
  log : Array String := #[]
  stats : RunStats := {}
  /-- Some `unsat` verdict came from a trusted solver. -/
  anyTrusted : Bool := false
  /-- A write to the log file failed and the warning has been shown. -/
  logFileFailed : Bool := false
  /-- The frontier structure most recently blocked at the current frontier;
  a frontier query that returns it again is a decoding bug (`mainLoop`). -/
  lastFrontier : Option FinStructure := none
  /-- States known to be reachable, each with its *depth*, the number of
  transitions from an initial state that reached it: a model of `init` (depth
  0), the states of the bounded executions sampled before the search (state
  `i` of a path has depth `i`), and both states of every level-one predecessor
  query (depths 0 and 1). A candidate clause false in one of them is discarded
  without a solver call (`generalize`); at level `j` only samples of depth at
  most `j` count, since a clause of frame `F_j` need hold only in states
  reachable in at most `j` steps. -/
  samples : Array (FinStructure × Nat) := #[]

abbrev SearchM := ReaderT Ctx (StateRefT St TermElabM)

def clauseJson (c : Clause) : Json :=
  Json.mkObj [("text", toString c), ("numVars", c.vars.size), ("numLits", c.lits.size)]

/-- Append one JSON object as a line of the log file, creating its directory. -/
def appendEvent (path : System.FilePath) (j : Json) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.withFile path .append fun h => h.putStrLn j.compress

/-- What the admission check of `generalize` says about a candidate clause. -/
inductive Admission where
  /-- Both admission queries answered `unsat`; `i` and `k` are those answers,
  kept for the `Admitted` record. -/
  | admissible (i k : QueryResult)
  /-- Rejected; `verdict` is the recorded reason, the `verdict` of the log's
  `candidate` event: `sampled_out` (false in a reachable sample, decided
  without a solver call), `not_initial` (an initial state violates it) or
  `has_predecessor` (a state of the frame below reaches its negation in one
  step). -/
  | rejected (verdict : String)
  /-- No answer (unknown, error, fuel), which is not evidence about the
  candidate. The pass that asked ends: the linear pass moves on to the
  cores, the other passes keep the last clause that passed. -/
  | noAnswer

/-- The rejection of a candidate in words, for the progress lines. -/
def Admission.describeRejection : String → String
  | "sampled_out" => "false in a reachable sample"
  | "not_initial" => "not admissible in clause form: an initial state violates it"
  | "has_predecessor" => "not admissible in clause form: it has a predecessor in the frame below"
  | v => v

namespace SearchM

/-- A progress line: kept in the run's log, shown as a message under `verbose`. -/
def say (msg : String) : SearchM Unit := do
  modify fun s => { s with log := s.log.push msg }
  if (← read).cfg.verbose then logInfo msg

/-- Record a structured event: appended to the log file at once when one is
configured. A failing write is reported once and does not stop the run. -/
def event (kind : String) (fields : List (String × Json)) : SearchM Unit := do
  let some path := (← read).cfg.logFile | return
  try appendEvent path (Json.mkObj (("event", kind) :: fields))
  catch e =>
    unless (← get).logFileFailed do
      logWarning m!"IC3: could not append to the log file {path}: {e.toMessageData}; later events are not logged"
      modify fun s => { s with logFileFailed := true }

def frameSizes : SearchM (Array Nat) := do return (← get).frames.map (·.size)

/-- Record states known to be reachable, with their depths, as samples for
the generalizers (`St.samples`). A state already recorded keeps the smaller
depth. -/
def addSamples (σs : Array (FinStructure × Nat)) : SearchM Unit := modify fun s =>
  { s with samples := σs.foldl (init := s.samples) fun acc (σ, d) =>
      match acc.findIdx? (·.1 == σ) with
      | some i => if d < acc[i]!.2 then acc.set! i (σ, d) else acc
      | none => acc.push (σ, d) }

/-- The samples a candidate at level `j` is screened against: those of depth
at most `j` (`St.samples`). -/
def samplesUpTo (j : Nat) : SearchM (Array FinStructure) := do
  return ((← get).samples.filter (·.2 ≤ j)).map (·.1)

/-- The `unknown` outcome with the current frame sizes. -/
def stop (reason : String) : SearchM Outcome := do return .unknown reason (← frameSizes)

/-- `P` together with the clauses of `frames[i]` (frame `F_{i+1}`). -/
def frameTerms (i : Nat) : SearchM (Array Term) := do
  let s ← get
  let clauses := (s.frames[i]?).getD #[]
  return (← read).property ++ clauses.map (·.term)

/-- Run a query, counting the call and its wall-clock time. The time by phase
is read from `queryPhases` once per run (`synthesize`). -/
def timed (act : TermElabM α) : SearchM α := do
  let t0 ← IO.monoMsNow
  let r ← (act : TermElabM α)
  let t1 ← IO.monoMsNow
  modify fun s => { s with stats := { s.stats with solverCalls := s.stats.solverCalls + 1, solverMs := s.stats.solverMs + (t1 - t0) } }
  return r

/-- Consume one unit of fuel; `false` when none is left. -/
def spend : SearchM Bool := do
  let s ← get
  if s.fuel == 0 then return false
  set { s with fuel := s.fuel - 1 }
  return true

def fuelMessage : SearchM String := do return s!"fuel exhausted ({(← read).cfg.fuel} solver calls)"

/-- Whether an answer is an `unsat` from a trusted solver. -/
def answeredByTrust : QueryResult → Bool
  | .unsat _ _ t => t
  | _ => false

def noteTrust (r : QueryResult) : SearchM Unit :=
  if answeredByTrust r then modify fun s => { s with anyTrusted := true } else pure ()

/-- Ask a statement, with `lits` trailing diagram literals for an unsat core
(`runStatementCore`). With `retry`, an answer the solver itself gave up on
(`QueryResult.solverGaveUp`: a timeout or an `unknown` verdict, not fuel or a
budget overrun) is asked once more with twice `veil.smt.timeout`, at the cost
of one more solver call: a fact at the edge of the solver's budget can fall
on either side of it, and one such answer should not end a long run. Only
the queries whose unknown answer stops the search pass `retry`. -/
def solveCore (stmt : Term) (k : Nat) (lits : Nat) (wantModel : Bool := true) (retry : Bool := false)
    : SearchM (QueryResult × Option (Array Nat)) := do
  unless ← spend do return (.unknown (← fuelMessage), none)
  let mod := (← read).qctx.mod
  let (r, core) ← timed (runStatementCore mod stmt k lits wantModel)
  noteTrust r
  unless retry && r.solverGaveUp do return (r, core)
  unless ← spend do return (.unknown (← fuelMessage), none)
  let t := veil.smt.timeout.get (← getOptions)
  say s!"the solver gave up ({(toString r).take 120}); asking again with veil.smt.timeout {2 * t}"
  let (r', core') ← timed (withOptions (fun o => veil.smt.timeout.set o (2 * t))
    (runStatementCore mod stmt k lits wantModel))
  noteTrust r'
  return (r', core')

/-- `solveCore` without diagram literals. -/
def solve (stmt : Term) (k : Nat) (wantModel : Bool := true) (retry : Bool := false) : SearchM QueryResult :=
  (·.1) <$> solveCore stmt k 0 wantModel retry

/-- `F_{j-1} ∧ tr ∧ ¬post'`: a predecessor of `¬post` states in the frame
below `j`. `F₀` is `init`; `F_i` for `i ≥ 1` is `frames[i-1]` plus `P`. -/
def stepQuery (j : Nat) (post : Term) (wantModel : Bool := true) : SearchM QueryResult := do
  let qctx := (← read).qctx
  if j == 0 then
    -- An obligation at level 0 is resolved without a query; asking for a
    -- predecessor below `init` is a controller bug.
    throwError "IC3: predecessor query below frame 0"
  if j == 1 then
    solve (← qctx.twoState #[] post (withInit := true)) 1 wantModel
  else
    solve (← qctx.twoState (← frameTerms (j - 2)) post) 1 wantModel

/-- `init ∧ ¬post`. -/
def initQuery (post : Term) (wantModel : Bool := true) (retry : Bool := false) : SearchM QueryResult := do
  solve (← (← read).qctx.oneState true #[] post) 0 wantModel retry

/-- Ask `query p` for each conjunct `p` of the property in turn and stop at
the first answer that is not `unsat`: a `sat` answer is a state violating
that conjunct, an `unknown` or `error` answer stops the search. When every
conjunct passes, the last `unsat` is returned. One negated conjunct per
query is what Veil's `#check_invariants` asks and what the certificate
re-asks; negating the whole conjunction in one query puts every conjunct's
negation in one disjunction, and the negation of an existential conjunct is
a universal-existential formula, which the solver handles far better one at
a time. -/
def perConjunct (query : Term → SearchM QueryResult) : SearchM QueryResult := do
  let mut last : Option QueryResult := none
  for p in (← read).propertyConjuncts do
    let r ← query p
    match r with
    | .unsat .. => last := some r
    | _ => return r
  match last with
  | some r => return r
  | none => throwError "IC3: the property has no conjuncts"

/-- The frontier query `F_N ∧ tr ∧ ¬p'`, one property conjunct `p` at a time. -/
def frontierQuery (N : Nat) : SearchM QueryResult := do
  let qctx := (← read).qctx
  let pre ← frameTerms (N - 1)
  perConjunct fun p => do solve (← qctx.twoState pre p) 1 (retry := true)

def decode (j : Json) : SearchM DecodedTrace := do
  match decodeTrace (← read).sig j with
  | .ok dt =>
    unless dt.completed.isEmpty do
      trace[veil.synthesizer.debug] "IC3: the model did not mention {dt.completed}; default tables were used"
    return dt
  | .error e => throwError "IC3: could not decode a solver model: {e}"

/-- The outcome of a query whose `sat` answer is an execution of `steps`
transitions violating `P`: the decoded execution, or `unsafeUndecoded` when
the model could not be read, by Veil's decoder (`QueryResult.satUndecoded`)
or by `decodeTrace`. The violation stands either way. -/
def violation (steps : Nat) (r : QueryResult) : SearchM Outcome := do
  match r with
  | .sat m =>
    try return .«unsafe» (← decode m)
    catch e => return .unsafeUndecoded steps ((← e.toMessageData.toString).take 300).toString
  | .satUndecoded reason => return .unsafeUndecoded steps reason
  | _ => throwError "IC3: a violation was reported from an answer that is not sat ({r})"

/-- Literal terms of a diagram (positive literals of `Diag(σ)`), that is the
negations of the blocking clause's literals, rendered for the query builders. -/
def diagramLiteralTerms (c : Clause) : TermElabM (Array Term) :=
  c.lits.mapM fun l => l.negate.toTerm

/-- The order in which generalization tries to drop literals, cheapest first:
the values a counterexample happened to have (numeral literals), then
equalities between variables and constants of instantiated classes
(`tom.zero = x0`), then function-graph facts, then relations of instantiated
classes (`tom.le`), then the module's own state. Dropping constants and
function facts before order relations is what lets a chain "x is the k-th
successor of zero" generalize to an order clause. -/
def literalRank (l : Literal) : Nat := match l.atom with
  | .lin .. => if l.atom.isNumeral then 0 else 2
  | .eq .. => 1
  | .rel sym _ => match sym.source with
    | .typeclassConst .. => 1
    | .typeclassFn .. | .function | .individualEq => 2
    | .typeclassField .. => 3
    | .state | .boolIndividual => 4

/-- Drop literals of an admissible clause while it stays admissible (Section
4.3 of the paper asks for a clause from a minimal unsat core, disjoint from
`init` and without predecessor; this pass makes the core-derived clause
smaller in that sense). Literals are grouped by rank (`literalRank`) and the
ranks are tried cheapest first. Within a rank the whole group of remaining
literals is dropped at once; when that clause is not admissible the group is
split in halves and each half is tried the same way, down to single literals,
the descent of delta debugging (a method that finds a small failing subset by
halving). A group that would empty the clause is split without a try. A
deletion is kept only when both admission queries answer `unsat`, so what
comes out is admissible whatever the grouping. The number of tries is bounded
by twice the number of literals: a descent that drops nothing costs at most
`2m - 1` tries for a group of `m` literals (one fewer when the group is the
whole clause, whose root is split without a try), so under that bound every
single literal is still tried, as it was when this pass tried one literal at
a time, and the result is again minimal one literal at a time relative to the
answers. A missing answer ends the pass. -/
def minimize (j : Nat) (c : Clause) (i k : QueryResult)
    (check : Clause → SearchM Admission)
    : SearchM (Clause × QueryResult × QueryResult) := do
  let mut ev := (i, k)
  let mut keep : Array Bool := Array.replicate c.lits.size true
  let build (mask : Array Bool) : Clause :=
    ({ c with lits := (c.lits.zip mask).filterMap fun (l, k) => if k then some l else none } : Clause)
  let ranks := (c.lits.map literalRank).qsort (· < ·) |>.foldl (fun acc r => if acc.contains r then acc else acc.push r) #[]
  let maxTries := 2 * c.lits.size
  let mut tries := 0
  let mut stopped := false
  for r in ranks do
    if stopped then break
    -- Groups still to try, the one to try first in front.
    let mut work : List (Array Nat) := [(Array.range c.lits.size).filter fun idx => literalRank c.lits[idx]! == r]
    while !work.isEmpty do
      let g :: rest := work | break
      work := rest
      let g := g.filter (keep[·]!)
      if g.isEmpty then continue
      let halves (g : Array Nat) : List (Array Nat) :=
        if g.size ≥ 2 then [g.extract 0 (g.size / 2), g.extract (g.size / 2) g.size] else []
      if g.size ≥ (keep.filter id).size then
        work := halves g ++ work
        continue
      if tries ≥ maxTries then
        stopped := true
        break
      tries := tries + 1
      let mask' := g.foldl (fun m idx => m.set! idx false) keep
      match ← check (build mask').pruneVars with
      | .admissible i' k' => keep := mask'; ev := (i', k')
      | .noAnswer =>
        stopped := true
        break
      | .rejected _ => work := halves g ++ work
  let cur := build keep
  let dropped := c.lits.size - cur.lits.size
  if dropped > 0 then say s!"level {j}: minimization dropped {dropped} more literal(s) in {tries} tries"
  return (cur.pruneVars, ev.1, ev.2)

/-- Generalize `¬Diag(σ)` relative to frame `j` (Section 4.3 of the paper,
"generalization of blocked diagrams"): find a sub-diagram `Diag_L ⊆ Diag(σ)`
that is still disjoint from `init` and has no predecessor in `F_{j-1}`; then
`¬Diag_L` is the blocking clause, and it excludes more states than `¬Diag(σ)`.

A candidate is *admissible* when the two clause-form queries `init ∧ ¬c` and
`F_{j-1} ∧ tr ∧ ¬c'` are both unsatisfiable. The flow:

* Before any solver call a candidate is evaluated on the reachable samples
  of depth at most `j` (`St.samples`); one that is false in such a sample
  cannot belong to `F_j` and is recorded as `sampled_out`. Deeper samples are
  not consulted here: a clause they falsify can still be admissible relative
  to the frame below, and the paper's generalizer admits such clauses (the
  linear templates filter their own candidates on every sample, since the
  relations they look for are meant as invariants).
* The caller asked those two questions about the full diagram in skolemized
  form and hands over the answers with their unsat cores, the sets of diagram
  literals the solver used. The union of the cores is the first candidate. It
  is checked with two solver calls and, when admissible and longer than two
  literals, minimized by group deletion (`minimize`).
* No answer for that candidate (unknown, error or fuel) keeps the raw clause.
* A candidate that is rejected, in clause form or on a sample, cores that are
  empty or cover every literal, and missing cores fall to greedy deletion:
  literals are tried in rank order (equalities, then typeclass literals, then
  state literals), each deletion kept when the clause stays admissible, at
  most forty tries.
* With generalization off the full negated diagram is returned. -/
def generalize (j : Nat) (σ : FinStructure) (c0 : Clause) (rawI rawK : QueryResult)
    (iCore kCore : Option (Array Nat)) : SearchM (Clause × QueryResult × QueryResult) := do
  -- Admissibility of a candidate clause (`Admission`): admissible with its
  -- two verdicts, rejected with the recorded reason, or no answer.
  let check (gen : String) (c : Clause) : SearchM Admission := do
    let t ← c.toTerm
    let record (verdict : String) (reason : String := "") :=
      event "candidate" [("level", j), ("clause", clauseJson c), ("verdict", verdict), ("from", clauseJson c0), ("generalizer", gen), ("reason", reason)]
    let noAnswer (query : String) (r : String) : SearchM Admission := do
      say s!"level {j}: no solver answer for candidate {c} ({query}: {r.take 160})"
      record "unknown" s!"{query}: {r.take 300}"
      return .noAnswer
    -- A candidate false in a reachable sample of depth at most `j` cannot be
    -- a clause of `F_j`, so it is rejected without a solver call. A sample is
    -- a finite structure at its own sort sizes and a universal clause is
    -- evaluated over the sample's elements only: that rejects soundly (a
    -- clause false in a reachable state at some sizes holds in no frame that
    -- contains the state) and admits nothing.
    if (← samplesUpTo j).any fun σ => !σ.models c then
      record "sampled_out"
      return .rejected "sampled_out"
    let i ← initQuery t (wantModel := false)
    match i with
    | .sat _ | .satUndecoded _ => record "not_initial"; return .rejected "not_initial"
    | .unknown r => return ← noAnswer "initiation" r
    | .error r => return ← noAnswer "initiation" r
    | .unsat .. => pure ()
    let k ← stepQuery j t (wantModel := false)
    match k with
    | .sat _ | .satUndecoded _ => record "has_predecessor"; return .rejected "has_predecessor"
    | .unknown r => return ← noAnswer "consecution" r
    | .error r => return ← noAnswer "consecution" r
    | .unsat .. => pure ()
    record "admissible"
    return .admissible i k
  -- The raw blocking clause `¬Diag(σ)` is admissible by construction: the
  -- caller established `init ∧ Diag(σ)` and `F_{j-1} ∧ tr ∧ Diag(σ)'` unsat in
  -- skolemized form and hands over those verdicts with their unsat cores.
  if !(← read).cfg.generalize then return (c0, rawI, rawK)
  -- Linear templates first, on a module with integer state: a relation
  -- between counters that σ violates and every reachable sample satisfies.
  let ctx ← read
  if ctx.cfg.generalizer == .linear && !ctx.sig.numericSorts.isEmpty then
    let cands := Linear.candidates σ ctx.sig.numerals ((← get).samples.map (·.1))
    say s!"level {j}: {cands.size} linear candidate(s), trying at most {ctx.cfg.maxLinear}"
    let mut tried := 0
    for c in cands do
      if tried ≥ ctx.cfg.maxLinear then break
      tried := tried + 1
      match ← check "linear" c with
      | .admissible i k =>
        say s!"level {j}: linear template admitted: {c}"
        return (c, i, k)
      | .noAnswer => break
      | .rejected _ => pure ()
  match (if ctx.cfg.cores then kCore else none), iCore with
  | some kc, some ic =>
    let keep := (Array.range c0.lits.size).filter fun i => kc.contains i || ic.contains i
    if keep.size < c0.lits.size && !keep.isEmpty then
      let c := ({ c0 with lits := keep.map (c0.lits[·]!) } : Clause).pruneVars
      match ← check "updr" c with
      | .admissible i k =>
        say s!"level {j}: core kept {c.lits.size} of {c0.lits.size} literals"
        -- A clause of one or two literals is admitted as it is: the
        -- minimization pass would spend two calls per literal to gain little.
        if c.lits.size ≤ 2 then return (c, i, k)
        return (← minimize j c i k (check "updr"))
      | .noAnswer =>
        say s!"level {j}: no solver answer for the core-derived clause; keeping the raw clause"
        return (c0, rawI, rawK)
      | .rejected v =>
        say s!"level {j}: core-derived clause ({c.lits.size} literals) was {Admission.describeRejection v}; falling back to deletion"
    else
      say s!"level {j}: the unsat cores {if keep.isEmpty then "are empty" else "cover every literal"}; falling back to deletion"
  | _, _ =>
    say s!"level {j}: {if ctx.cfg.cores then "no unsat cores; falling back to deletion" else "deletion from the full diagram, cheapest literals first"}"
  -- Fallback: greedy literal deletion from the raw clause, cheapest literals
  -- first. Each surviving deletion is re-checked in clause form.
  let order := (Array.range c0.lits.size).qsort fun a b => literalRank c0.lits[a]! < literalRank c0.lits[b]!
  let mut keep : Array Bool := Array.replicate c0.lits.size true
  let build (mask : Array Bool) : Clause :=
    ({ c0 with lits := (c0.lits.zip mask).filterMap fun (l, k) => if k then some l else none } : Clause).pruneVars
  let mut ev := (rawI, rawK)
  -- Cap the fallback so a huge diagram cannot spend the whole budget here;
  -- without cores every literal is tried once.
  let maxTries := if ctx.cfg.cores then 40 else c0.lits.size
  let mut tries := 0
  for idx in order do
    if tries ≥ maxTries then break
    tries := tries + 1
    let mask' := keep.set! idx false
    let c' := build mask'
    if c'.lits.isEmpty then continue
    match ← check "updr" c' with
    | .admissible i' k' => keep := mask'; ev := (i', k')
    | .noAnswer => break
    | .rejected _ => pure ()
  return (build keep, ev.1, ev.2)

/-- Insert `a` into a frame's clause set: skip it when a clause of the frame
already subsumes it, otherwise add it and drop the clauses it subsumes (they
follow from `a`). Subsumption is up to variable renaming (`Clause.subsumes`). -/
def insertSubsuming (cs : Array Admitted) (a : Admitted) : Array Admitted :=
  if cs.any (·.clause.subsumes a.clause) then cs
  else (cs.filter fun d => !a.clause.subsumes d.clause).push a

/-- Add `a` to `F₁ … F_upto` with `insertSubsuming`. -/
def addClause (upto : Nat) (a : Admitted) : SearchM Unit := modify fun s =>
  { s with frames := (Array.range upto).foldl (init := s.frames) fun fr i =>
      if i < fr.size then fr.modify i (insertSubsuming · a) else fr }

/-- Whether some clause of `frames[i]` subsumes `c`. -/
def containsClause (i : Nat) (c : Clause) : SearchM Bool := do
  let s ← get
  return ((s.frames[i]?).getD #[]).any (·.clause.subsumes c)

/-- A clause of `F_{j-1}` that `σ` violates and that is inductive relative to
`F_{j-1}`: pushing it to `F_j` blocks `σ` with one solver call. Only clauses
of the frame below are tried (they are the ones a push would move), newest
first, at most two. Initiation was established when the clause was admitted. -/
def reuseFromBelow (j : Nat) (σ : FinStructure) : SearchM (Option Admitted) := do
  if j < 2 then return none
  let s ← get
  let below := (s.frames[j - 2]?).getD #[]
  let mut tries := 0
  for a in below.reverse do
    if tries ≥ 2 then break
    if σ.models a.clause then continue
    if ← containsClause (j - 1) a.clause then continue
    tries := tries + 1
    let r ← stepQuery j a.term (wantModel := false)
    if let .unsat .. := r then return some { a with viaTrust := a.viaTrust || answeredByTrust r }
  return none

/-- The abstract counterexample `diagrams` (the structure at level `j` first,
the frontier structure last) reaches `init` at level `j`. By Prop. 5.6 no
universal inductive invariant proves `P`, whatever the bounded checks say:
such an invariant `I` holds in an initial state that contains the first
structure as a substructure, hence in that structure (the state contains it
as a substructure by Lemma 4.3, and universal sentences pass to
substructures closed under the function symbols, which the graph literals of
the diagram guarantee); inductiveness carries it to a
successor, which contains the next structure, and so on up to the frontier
structure, whose successor violates `P`. When `j = 0` the chain describes a
concrete candidate path of `N + 1` transitions, which a bounded check can
confirm as a real counterexample. For `j ≥ 1` the path would have at most `N`
transitions; `init ∧ tr ∧ ¬P'` was checked before the loop and frame `N - 1`
was clear, so no such path exists and no check is run.

The paper states Proposition 5.6 for a vocabulary of constants and relations
over uninterpreted sorts. This tool extends it to function symbols, sort-
valued class fields and enum sorts by the argument above (the graph literals
keep the embedded copy closed under the functions; an enum carrier is fixed),
and does not extend it to integer terms: with integer state in the vocabulary
the chain is reported as `Outcome.absenceWithheld`, a stopped run that shows
the chain and what the bounded check said, and no verdict is given. -/
def analyzeCEX (N j : Nat) (diagrams : Array FinStructure) : SearchM Outcome := do
  let ctx ← read
  let mut check : BoundedCheck := .notAsked
  if j == 0 then
    let k := N + 1
    say s!"bounded path check of length {k}"
    let q ← ctx.qctx.boundedPath k ctx.propertyTerm
    match ← solve q k (retry := true) with
    | r@(.sat _) | r@(.satUndecoded _) => return ← violation k r
    | .unsat .. => check := .noPath k
    | .unknown r =>
      say s!"bounded path check returned unknown ({r}); the abstract counterexample stands"
      check := .noAnswer k s!"unknown: {r}"
    | .error e =>
      say s!"bounded path check failed ({e}); the abstract counterexample stands"
      check := .noAnswer k s!"error: {e}"
  if !ctx.sig.numericSorts.isEmpty then
    return .absenceWithheld diagrams check (← frameSizes)
  return .noUniversalInvariant diagrams check

/-- An entry of the obligation stack: frame `level` must exclude `σ`.
`lastPredecessor` is the predecessor most recently found for it. Discharging
that predecessor added a clause it violates to the frame below (or ended the
search), so a predecessor query that returns it again is a decoding bug; this
is the counterpart of `St.lastFrontier` for the frontier query. -/
structure Obligation where
  level : Nat
  σ : FinStructure
  lastPredecessor : Option FinStructure := none

/-- Discharge the obligation stack. `N` is the frontier index (1-based). -/
partial def discharge (N : Nat) (stack : List Obligation) : SearchM (Option Outcome) := do
  match stack with
  | [] => return none
  | ob :: rest =>
    let j := ob.level
    let σ := ob.σ
    -- A level-0 obligation is the pre-state of a predecessor query against
    -- `init`, so it is contained in an initial state (Algorithm 2, line 22
    -- for j = 0; Section 4.3). No query is needed.
    if j == 0 then
      say "level 0: the structure is contained in an initial state"
      return some (← analyzeCEX N 0 (stack.map (·.σ)).toArray)
    let ctx ← read
    let diagClause := σ.negatedDiagram
    -- Diagrams are asked about in skolemized form (one conjunct per literal):
    -- far cheaper to preprocess than a nested existential, and the unsat
    -- cores it yields drive generalization.
    let vars := diagClause.vars
    let lits ← diagramLiteralTerms diagClause
    -- A clause of the frame below that already excludes σ and is inductive
    -- relative to F_{j-1} blocks σ with one solver call.
    if let some a ← reuseFromBelow j σ then
      say s!"level {j}: reused {a.clause}"
      event "reused" [("level", j), ("frontier", N), ("diagram", clauseJson diagClause), ("clause", clauseJson a.clause)]
      addClause j a
      return ← discharge N rest
    -- Predecessor of Diag(σ) in F_{j-1}? Asked before the init check: when a
    -- predecessor exists the search descends and the init check would be
    -- wasted (for j ≥ 2 the paper's Lemma 4.8 makes it redundant anyway).
    let pre ← if j == 1 then pure #[] else frameTerms (j - 2)
    let (kRes, kCore) ← solveCore (← ctx.qctx.twoStateLits pre vars lits (withInit := j == 1)) 1 lits.size
      (retry := true)
    match kRes with
    | .sat m =>
      let dt ← decode m
      let σ' := dt.states[0]!
      -- Discharging the previous predecessor added a clause to F_{j-1} that
      -- it violates, so a correct model of this query cannot decode to it.
      if ob.lastPredecessor == some σ' then
        throwError "IC3: the predecessor query returned the structure just blocked at level {j - 1}; a model symbol was decoded or completed wrongly"
      -- At level one the pre-state is initial and the post-state one step
      -- from it: both are reachable, and samples for the linear templates.
      if j == 1 && dt.states.size ≥ 2 then
        addSamples #[(dt.states[0]!, 0), (dt.states[1]!, 1)]
      say s!"level {j}: predecessor found in F_{j-1}; descending"
      discharge N ({ level := j - 1, σ := σ' } :: { ob with lastPredecessor := some σ' } :: rest)
    | .satUndecoded r => return some (← stop s!"predecessor query answered sat, but its model could not be decoded: {r}")
    | .unknown r => return some (← stop s!"predecessor query unknown: {r}")
    | .error e => return some (← stop s!"predecessor query failed: {e}")
    | .unsat .. =>
      -- Is a state of Diag(σ) initial? Needed as a verdict at j = 1 (line 22)
      -- and, at every level, for the unsat core that drives generalization.
      let (iRes, iCore) ← solveCore (← ctx.qctx.initLits vars lits) 0 lits.size (wantModel := false)
        (retry := true)
      match iRes with
      | .sat _ | .satUndecoded _ =>
        say s!"level {j}: Diag(σ) meets init"
        return some (← analyzeCEX N j (stack.map (·.σ)).toArray)
      | .unknown r => return some (← stop s!"init check unknown: {r}")
      | .error e => return some (← stop s!"init check failed: {e}")
      | .unsat .. => pure ()
      let (c, i, k) ← generalize j σ diagClause iRes kRes iCore kCore
      -- Every candidate is cut from `¬Diag(σ)`, so a clause that `σ`
      -- satisfies is a bug in a generalizer, reported as an internal error.
      if σ.models c then
        throwError "IC3: the admitted clause does not exclude the structure it was cut from ({c}); a generalizer produced a clause outside the negated diagram"
      event "admitted" [("level", j), ("frontier", N), ("diagram", clauseJson diagClause), ("clause", clauseJson c),
        ("frameSizes", toJson (← frameSizes))]
      say s!"level {j}: admitted ({c.numLits} of {diagClause.numLits} literals kept) {c}"
      addClause j { clause := c, term := ← c.toTerm, viaTrust := answeredByTrust i || answeredByTrust k }
      discharge N rest

/-- Push clauses of `F_i` into `F_{i+1}` for every `i ≤ N` (`F_{N+1}` has just
been opened). A clause `c ∈ F_i` that no clause of `F_{i+1}` subsumes moves up
when `F_i ∧ tr ⇒ c'`, dropping the clauses of `F_{i+1}` it subsumes. Returns
the first level `i` at which every clause of `F_i` was pushed or already
subsumed, so that `F_i = F_{i+1}` and that frame is inductive; propagation
stops there. -/
def propagate (N : Nat) : SearchM (Option Nat) := do
  let qctx := (← read).qctx
  for i in [1:N+1] do
    let fromClauses := ((← get).frames[i - 1]?).getD #[]
    let mut allPushed := true
    for a in fromClauses do
      if ← containsClause i a.clause then continue
      let r ← solve (← qctx.twoState (← frameTerms (i - 1)) a.term) 1 (wantModel := false)
      match r with
      | .unsat .. =>
        let a' := { a with viaTrust := a.viaTrust || answeredByTrust r }
        modify fun s => { s with frames := s.frames.modify i (insertSubsuming · a') }
      -- Propagation is an optimization (footnote 5 of the paper): a clause
      -- that cannot be shown inductive, or that gets no answer, is not pushed.
      | _ => allPushed := false
    if allPushed then return some i
  return none

/-- Drop every clause of a frame that another clause of the frame subsumes
(`Clause.removeSubsumed`). -/
def removeSubsumedAdmitted (fr : Array Admitted) : Array Admitted := Id.run do
  let mut remaining := Clause.removeSubsumed (fr.map (·.clause))
  let mut out := #[]
  for a in fr do
    if let some idx := remaining.findIdx? (· == a.clause) then
      out := out.push a
      remaining := remaining.eraseIdx! idx
  return out

/-- One frontier at a time: block every bad state of `F_N`, then open
`F_{N+1}`, propagate, and stop at a fixpoint or a verdict. -/
partial def mainLoop (N : Nat) : SearchM Outcome := do
  let ctx ← read
  if N > ctx.cfg.maxFrames then return ← stop s!"frame limit reached ({ctx.cfg.maxFrames} frames)"
  -- Frontier: F_N ∧ tr ∧ ¬p' for each conjunct p of P.
  match ← frontierQuery N with
  | .sat m =>
    let dt ← decode m
    let σ := dt.states[0]!
    -- Blocking σ added a clause to `F_N` that σ violates, so a correct model
    -- of the next frontier query cannot decode to σ again; a repeat means a
    -- symbol was decoded or completed wrongly (`defaultTable`).
    if (← get).lastFrontier == some σ then
      throwError "IC3: the frontier query returned the structure just blocked; a model symbol was decoded or completed wrongly"
    modify fun s => { s with lastFrontier := some σ }
    say s!"frame {N}: bad state found; blocking"
    match ← discharge N [{ level := N, σ }] with
    | some outcome => return outcome
    | none => mainLoop N
  | .satUndecoded r => stop s!"frontier query answered sat, but its model could not be decoded: {r}"
  | .unknown r => stop s!"frontier query unknown: {r}"
  | .error e => stop s!"frontier query failed: {e}"
  | .unsat .. =>
    say s!"frame {N} is clear; opening frame {N + 1}"
    event "frame_clear" [("frame", N), ("frameSizes", toJson (← frameSizes))]
    -- A structure blocked at `F_N` may be a genuine model at `F_{N+1}`.
    modify fun s => { s with frames := s.frames.push #[], lastFrontier := none }
    match ← propagate N with
    | some i =>
      let s ← get
      say s!"frame {i} equals frame {i + 1}: fixpoint"
      return .foundInvariant i (removeSubsumedAdmitted s.frames[i - 1]!) s.anyTrusted
    | none => mainLoop (N + 1)

end SearchM

/-- The conjuncts of the property `P`: the module's `safety` clauses and, when
`useDeclaredInvariants` is set, its declared `invariant`s (not `safety` again,
not `trusted invariant`s, which Veil assumes rather than checks). -/
def propertyConjuncts (mod : Veil.Module) (cfg : Config) : Array Term :=
  let safeties := mod.safeties.map (·.term)
  let invariants := if cfg.useDeclaredInvariants
    then (mod.assertions.filter (·.kind == .invariant)).map (·.term) else #[]
  safeties ++ invariants

/-- The conjuncts of `P` (`propertyConjuncts`), or the error a module without
any gets. -/
def checkedProperty (mod : Veil.Module) (cfg : Config) : CoreM (Array Term) := do
  let property := propertyConjuncts mod cfg
  if property.isEmpty then
    throwError "IC3: the module declares no safety property{if cfg.useDeclaredInvariants then "" else " (use `(invariants := true)` to work on its declared invariants)"}"
  return property

/-- Run UPDR on the current module's property. `sig` is the module's
vocabulary (`Signature.ofModule`), computed once by the command, which
rejects unsupported modules with it before anything runs and reads it again
for the verdict messages. -/
def synthesize (mod : Veil.Module) (cfg : Config) (sig : Signature) : TermElabM RunResult := do
  let qctx ← QueryCtx.ofModule mod
  let property ← checkedProperty mod cfg
  -- Capitals quantified per conjunct (the same capital may name different sorts).
  let propertyConjuncts ← property.mapM fun t => `(term| (uqc% (($t:term):Prop)))
  let propertyTerm ← repeatedAnd propertyConjuncts
  let ctx : Ctx := { cfg, qctx, sig, property, propertyConjuncts, propertyTerm }
  -- The state lives in a ref the caller owns, so the frames reached are
  -- still readable when the body throws.
  let ref ← IO.mkRef ({ fuel := cfg.fuel } : St)
  let phases0 ← queryPhases.get
  -- Initiation of P itself: init ∧ ¬p satisfiable for a conjunct p means the
  -- property fails at step 0. Both checks go one conjunct at a time (`perConjunct`).
  let body : SearchM Outcome := do
    -- Reachable samples for the linear templates: one initial state, then the
    -- states of one execution of each length up to `sampleDepth` (bounded
    -- paths from `init`), state `i` of a path at depth `i`. `sampleDepth + 1`
    -- solver calls (one for the initial state, one per path length); every
    -- state on such a path is reachable, so a candidate false in one of them
    -- is not an invariant. The samples save solver calls and decide nothing,
    -- so a query without a model or a model that does not decode is reported
    -- as a progress line and the run goes on with fewer samples.
    if cfg.generalizer == .linear && !sig.numericSorts.isEmpty then
      let addStates (q : Term) (k : Nat) : SearchM Unit := do
        try
          match ← SearchM.solve q k with
          | .sat m =>
            SearchM.addSamples ((← SearchM.decode m).states.mapIdx fun i σ => (σ, i))
          | .unsat .. => SearchM.say s!"no reachable sample of length {k}: no execution of that length"
          | r => SearchM.say s!"reachable sample of length {k} not collected ({(toString r).take 160})"
        catch e => SearchM.say s!"reachable sample of length {k} skipped ({((← e.toMessageData.toString).take 160).toString})"
      addStates (← qctx.oneState true #[] (← `(term| False))) 0
      for k in [1:cfg.sampleDepth + 1] do
        addStates (← qctx.boundedPath k (← `(term| False))) k
      SearchM.say s!"reachable samples for the linear templates: {(← get).samples.size}"
    match ← SearchM.perConjunct fun p => SearchM.initQuery p (retry := true) with
    | r@(.sat _) | r@(.satUndecoded _) => SearchM.violation 0 r
    | .unknown r => return Outcome.unknown s!"init ∧ ¬P unknown: {r}" #[]
    | .error e => return Outcome.unknown s!"init ∧ ¬P failed: {e}" #[]
    | .unsat .. =>
      -- One-step check `init ∧ tr ∧ ¬P'`: with it, "frame N-1 clear" holds for
      -- N = 1 too, which `analyzeCEX` relies on.
      match ← SearchM.perConjunct (fun p => do SearchM.solve (← qctx.twoState #[] p (withInit := true)) 1 (retry := true)) with
      | r@(.sat _) | r@(.satUndecoded _) => SearchM.violation 1 r
      | .unknown r => return Outcome.unknown s!"init ∧ tr ∧ ¬P' unknown: {r}" #[]
      | .error e => return Outcome.unknown s!"init ∧ tr ∧ ¬P' failed: {e}" #[]
      | .unsat .. => SearchM.mainLoop 1
  -- The whole run is one command elaboration; lift the command-level heartbeat
  -- budget. Solving is bounded by `veil.smt.timeout`, preprocessing by the
  -- per-query heartbeat budget in `Query.lean`, and the loop by fuel.
  let outcome ← withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) <|
    tryCatchRuntimeEx ((body.run ctx) ref) fun e => do
      let msg ← e.toMessageData.toString
      let s ← ref.get
      return Outcome.internalError (msg.take 400).toString (s.frames.map (·.size))
  let s ← ref.get
  return { outcome, stats := { s.stats with phases := (← queryPhases.get).sub phases0 }, log := s.log }

end Veil.Synthesizer
