module

public meta import Veil.Core.Tools.Synthesizer.Clause

/-!
# Linear templates

The paper's generalizer turns a counterexample structure into a universal
clause by dropping literals of its negated diagram. Over integer state that
produces clauses about the values the counterexample happened to have
(`¬ buffered = 3 ∨ ¬ consumed = 5`) and about their order, never a relation
between counters such as `buffered + consumed = produced`, because no literal
of the diagram says that. This file proposes such relations.

A candidate is a ground clause over the counterexample's numeric individuals
that the counterexample violates: a bound `x ≤ c`, a relation between two
individuals `x = y + c`, a sum `x + y = z`, or one of these guarded by a fact
of the counterexample about a `Bool` or enum individual (`¬ running ∨ attempt
= errors + 1`). Nothing here talks to the solver: the controller checks each
candidate for initiation and consecution and admits the first that passes,
exactly as it checks the clauses the paper's generalizer proposes. A
candidate can therefore cost time but not soundness.
-/

public meta section

namespace Veil.Synthesizer.Linear

/-- Numeric terms of a structure without arguments (`individual x : Int`), with
their values. Function terms need bound variables and are left to the
diagram. -/
def groundTerms (m : FinStructure) : Array (NumTerm × Int) :=
  m.nums.filterMap fun (sym, table) =>
    if sym.argSorts.size == 1 then
      (table.find? (·.1.isEmpty)).map fun (_, v) => (⟨sym, #[]⟩, v)
    else none

/-- Facts of the structure about its 0-ary non-numeric symbols, as positive
literals: a `Bool` individual that holds (or its negation when it does not),
and the value of an enum-valued individual. Used as guards. -/
def guardLiterals (m : FinStructure) : Array Literal :=
  m.rels.flatMap fun (sym, table) =>
    match sym.source, sym.argSorts.size with
    | .boolIndividual, 0 => #[{ positive := m.holds sym #[], atom := .rel sym #[] }]
    | .individualEq, 1 =>
      -- the table of a 0-ary function has one row: its value
      match table[0]?, table[0]?.bind fun row => row[0]? with
      | some _, some i =>
        match m.enumCtor? sym.argSorts[0]! i with
        | some ctor => #[{ positive := true, atom := .rel sym #[.enumConst ctor i] }]
        | none => #[]
      | _, _ => #[]
    | _, _ => #[]

/-- The template atoms over `terms` (all of one numeric sort) with the module
numerals `cs`, in the order to try them. Equalities come first because they
say the most and are refuted fastest when wrong: sums `x + y = z`, then
`x = y` and `x = y + c`; then the inequalities: `x ≤ y`, bounds `c ≤ x` and
`x ≤ c`, `x ≤ y + c`, and sums `x + y ≤ z`, `z ≤ x + y`. Within a group the
constant `0` comes before other constants, and smaller constants before
larger ones. -/
def templateAtoms (terms : Array NumTerm) (cs : Array Int) : Array Atom := Id.run do
  let cs := cs.qsort (fun a b => a.natAbs < b.natAbs)
  let nonzero := cs.filter (· != 0)
  let n := terms.size
  let mut out : Array Atom := #[]
  -- sums, equal
  for i in [:n] do
    for j in [i+1:n] do
      for k in [:n] do
        if k != i && k != j then out := out.push (.numSumEq terms[i]! terms[j]! terms[k]!)
  -- pairs, equal, constant 0 then others
  for i in [:n] do
    for j in [i+1:n] do
      out := out.push (.numEqOffset terms[i]! terms[j]! 0)
  for c in nonzero do
    for i in [:n] do
      for j in [:n] do
        if i != j then out := out.push (.numEqOffset terms[i]! terms[j]! c)
  -- pairs, ordered
  for i in [:n] do
    for j in [:n] do
      if i != j then out := out.push (.numLeOffset terms[i]! terms[j]! 0)
  -- bounds
  for c in cs do
    for t in terms do
      out := out.push (.numGe t c)
      out := out.push (.numLe t c)
  -- pairs with offset
  for c in nonzero do
    for i in [:n] do
      for j in [:n] do
        if i != j then out := out.push (.numLeOffset terms[i]! terms[j]! c)
  -- sums, ordered
  for i in [:n] do
    for j in [i+1:n] do
      for k in [:n] do
        if k != i && k != j then
          out := out.push (.numSumLe terms[i]! terms[j]! terms[k]!)
          out := out.push (.numLeSum terms[k]! terms[i]! terms[j]!)
  return out

/-- Candidate clauses for blocking `m`: ground template clauses over `m`'s
numeric individuals that `m` violates and that hold in every structure of
`samples`, unguarded ones first, then each guarded by one fact of `m` about a
`Bool` or enum individual. `samples` are states known to be reachable: a
model of `init`, the states of the bounded executions sampled before the
search, and both states of every level-one predecessor query (`St.samples`
in `Controller.lean`). Every sample is consulted whatever its depth, since
the relations the templates look for are meant as invariants, true in every
reachable state (the paper's generalizer screens by depth instead, see
`SearchM.generalize`); a clause false in one of them cannot be an invariant, so
it is not worth a solver call. `numerals` are the integer literals of the
module; `0` and `1` are always included. -/
def candidates (m : FinStructure) (numerals : Array Int) (samples : Array FinStructure := #[])
    : Array Clause := Id.run do
  let cs := (#[0, 1] ++ numerals).foldl (fun acc c => if acc.contains c then acc else acc.push c) #[]
  let ground := groundTerms m
  let sorts := (ground.map (·.1.sort)).foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]
  let mut atoms : Array Atom := #[]
  for s in sorts do
    atoms := atoms ++ templateAtoms ((ground.filter (·.1.sort == s)).map (·.1)) cs
  let worth (c : Clause) : Bool := !m.models c && samples.all (·.models c)
  let mut out : Array Clause := #[]
  let push (out : Array Clause) (c : Clause) : Array Clause :=
    if out.contains c then out else out.push c
  for a in atoms do
    let c : Clause := { vars := #[], lits := #[{ positive := true, atom := a }] }
    if worth c then out := push out c
  let guards := guardLiterals m
  for a in atoms do
    for g in guards do
      let c : Clause := { vars := #[], lits := #[g.negate, { positive := true, atom := a }] }
      if worth c then out := push out c
  return out

end Veil.Synthesizer.Linear
