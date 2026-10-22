module

public meta import Lean

/-!
# Clauses and finite structures for UPDR

The invariants UPDR builds are conjunctions of universal clauses. A clause is
a block of universally quantified variables (each with a sort) over a
disjunction of literals, where a literal is an atom or its negation. An atom
is a relation symbol applied to arguments, a function symbol applied to
arguments and equated to a result, or the equality of two variables.
The counterexamples it manipulates are finite first-order structures: a
finite domain per sort and, per symbol, the set of tuples that hold.

Both are plain data here. Nothing in this file knows about Veil; rendering a
clause to Veil syntax and reading a structure out of a solver model live in
`Render.lean` and `Vocabulary.lean`.

Design rule: a clause never names a concrete domain element of an
uninterpreted sort. Elements exist only inside `FinStructure`; a clause
refers to them through bound variables. That is what makes the negation of a
diagram (the existential description of a structure, `diagramLiterals` below)
a universal statement about every state, not a statement about one solver
model. The one kind of element a clause may name is a constructor of an enum
sort (`Arg.enumConst`). An enum sort has a fixed finite carrier whose elements
are named constants of the module, so naming one names a symbol of the
vocabulary, not an element of one model; diagrams never quantify over an enum
sort.

## Function symbols

A function `f : s₁ → … → sₙ → t` is represented by its graph: a symbol whose
argument sorts are `s₁ … sₙ t`, whose atom `rel f #[a₁, …, aₙ, b]` means
`f a₁ … aₙ = b`, and whose table in a structure has exactly one row per
argument tuple. A sort-valued individual `c` is the 0-ary case, `c = b`.
Because a table is total, the diagram of a structure states one positive
literal per argument tuple and no negative ones: `f ā ≠ b'` for another value
`b'` follows from `f ā = b` and `b ≠ b'`, where `b ≠ b'` is a diagram literal
when the result sort is uninterpreted and, when it is an enum sort, the
distinctness axiom of the enum's class, which every query carries as a
hypothesis. A constant (a 0-ary function) is the
exception: its negative facts are one per element, so they are kept, which
lets the generalizer keep `c = x` rather than `c ≠ y ∨ x = y`.
`RelSym.isFunction` tells the two readings of a symbol apart; evaluation and
subsumption need no distinction, since a graph is a relation.
-/

public meta section

namespace Veil.Synthesizer
open Lean

/-- A sort parameter of the module, by name (`node`). -/
abbrev SortName := Name

/-- Where a symbol comes from, which decides how it renders, whether it is
`Bool`- or `Prop`-valued in Veil's elaborated statements, and whether it is a
relation or a function (`RelSym.isFunction`). -/
inductive RelSource where
  /-- A `relation` of the module, mutable (`leader`, `pending`) or immutable.
  Veil renders these as `Bool`-valued fields: `leader x = true`. -/
  | state
  /-- A relation field of an instantiated typeclass (`tot.le`, `btwn.btw`):
  `inst` is the instance binder name, `field` the class field. `Prop`-valued. -/
  | typeclassField (inst : Name) (field : Name)
  /-- A `Bool`-valued `individual` (`abort_flag`), mutable or immutable: a 0-ary relation. -/
  | boolIndividual
  /-- An `individual` of a sort (`leader : node`), mutable or immutable: a
  0-ary function. The atom `rel c #[b]` means `c = b`. -/
  | individualEq
  /-- A sort-valued constant of an instantiated typeclass (`tot.zero`): a
  0-ary function like `individualEq`. The atom `rel tot.zero #[b]` means
  `tot.zero = b`. -/
  | typeclassConst (inst : Name) (field : Name)
  /-- A sort-valued `function` of the module (`curEpoch : node → epoch`),
  mutable or immutable, as its graph: the atom `rel f (args.push b)` means
  `f args = b`. -/
  | function
  /-- A sort-valued function field of an instantiated typeclass (`sc.next`),
  as its graph like `function`. -/
  | typeclassFn (inst : Name) (field : Name)
deriving Repr, BEq, Hashable, Inhabited

/-- A relation or function symbol with its argument sorts; for a function the
last argument sort is the result sort. Whether a module component is mutable
or immutable is recorded by the `Signature` that lists it, not here. -/
structure RelSym where
  name : Name
  source : RelSource
  argSorts : Array SortName
deriving Repr, BEq, Hashable, Inhabited

/-- Display name used in structures, logs and as a stable key
(`leader`, `tot.le`). -/
def RelSym.key (r : RelSym) : Name :=
  match r.source with
  | .state | .boolIndividual | .individualEq | .function => r.name
  | .typeclassField inst field | .typeclassConst inst field | .typeclassFn inst field => inst ++ field

/-- Whether the symbol is a function symbol read through its graph: the last
argument position is the result, and its table is total. -/
def RelSym.isFunction (r : RelSym) : Bool :=
  match r.source with
  | .individualEq | .typeclassConst .. | .function | .typeclassFn .. => true
  | _ => false

/-- The numeric sorts: `Int` and `Nat`. They have no elements in a structure;
see `NumTerm`. -/
def isNumericSort (s : SortName) : Bool := s == `Int || s == `Nat

/-- Whether the symbol's result is a numeric sort: `individual x : Int`,
`function f : node → Nat`. Its table lives in `FinStructure.nums`. -/
def RelSym.isNumeric (r : RelSym) : Bool :=
  r.isFunction && (r.argSorts.back?.map isNumericSort).getD false

/-- A bound variable of a clause, by index into `Clause.vars`. -/
abbrev Var := Nat

/-- An argument of an atom: a clause variable, or a constructor of an enum
sort, named by its constructor (`red`) and its position in the constructor
list, which is its element index in every structure. -/
inductive Arg where
  | var (v : Var)
  | enumConst (ctor : Name) (idx : Nat)
deriving Repr, BEq, Hashable, Inhabited

/-- A constructor's own name, without the enum class a clause may write it
through (`roleT_EnumClass.leader` is `leader`), as a solver model names it. -/
def _root_.Lean.Name.ctorBase (n : Name) : String := (n.updatePrefix .anonymous).toString

/-- Numerals denote variables: `#[0, 1]` is `#[.var 0, .var 1]`. -/
instance : OfNat Arg n := ⟨.var n⟩

def Arg.rename (ρ : Var → Var) : Arg → Arg
  | .var v => .var (ρ v)
  | a => a

/-- A term of a numeric sort (`Int` or `Nat`): a numeric-valued symbol applied
to arguments, `f x0` for `function f : node → Int`, or just `x` for
`individual x : Int`. Numeric sorts have no clause variables and no elements:
a structure records the value of each numeric term, and diagrams speak about
terms, numerals and the order between terms, as Ivy does
(`ivy_solver.py`, `numeral_assign`). -/
structure NumTerm where
  sym : RelSym
  args : Array Arg
deriving Repr, BEq, Hashable, Inhabited

/-- The numeric sort of a term: the result sort of its symbol. -/
def NumTerm.sort (t : NumTerm) : SortName := t.sym.argSorts.back!

/-- An atomic formula of a clause: a symbol applied to arguments (for a
function symbol, the last argument is the result), the equality of two
clause variables, or a linear constraint over numeric terms of one sort,
`Σ cᵢ·tᵢ + const = 0` when `isEq` and `Σ cᵢ·tᵢ + const ≤ 0` otherwise. -/
inductive Atom where
  | rel (sym : RelSym) (args : Array Arg)
  | eq (a b : Var)
  | lin (terms : Array (Int × NumTerm)) (const : Int) (isEq : Bool)
deriving Repr, BEq, Hashable, Inhabited

namespace Atom

/-- `t = n`. -/
def numEq (t : NumTerm) (n : Int) : Atom := .lin #[(1, t)] (-n) true
/-- `t ≤ n`. -/
def numLe (t : NumTerm) (n : Int) : Atom := .lin #[(1, t)] (-n) false
/-- `n ≤ t`. -/
def numGe (t : NumTerm) (n : Int) : Atom := .lin #[(-1, t)] n false
/-- `s < t`, written `s + 1 ≤ t`. -/
def numLt (s t : NumTerm) : Atom := .lin #[(1, s), (-1, t)] 1 false
/-- `s = t + c`. -/
def numEqOffset (s t : NumTerm) (c : Int) : Atom := .lin #[(1, s), (-1, t)] (-c) true
/-- `s ≤ t + c`. -/
def numLeOffset (s t : NumTerm) (c : Int) : Atom := .lin #[(1, s), (-1, t)] (-c) false
/-- `s + t = u`. -/
def numSumEq (s t u : NumTerm) : Atom := .lin #[(1, s), (1, t), (-1, u)] 0 true
/-- `s + t ≤ u`. -/
def numSumLe (s t u : NumTerm) : Atom := .lin #[(1, s), (1, t), (-1, u)] 0 false
/-- `u ≤ s + t`. -/
def numLeSum (u s t : NumTerm) : Atom := .lin #[(1, u), (-1, s), (-1, t)] 0 false

/-- Whether the atom is a numeral literal `t = n` or `t ≤ n`: the first thing
generalization tries to drop. -/
def isNumeral : Atom → Bool
  | .lin terms _ _ => terms.size == 1
  | _ => false

end Atom

/-- An atom or its negation. -/
structure Literal where
  positive : Bool
  atom : Atom
deriving Repr, BEq, Hashable, Inhabited

def Literal.negate (l : Literal) : Literal := { l with positive := !l.positive }

/-- Apply a variable substitution to a literal. -/
def NumTerm.rename (ρ : Var → Var) (t : NumTerm) : NumTerm := { t with args := t.args.map (Arg.rename ρ) }

def Literal.rename (ρ : Var → Var) (l : Literal) : Literal :=
  { l with atom := match l.atom with
    | .rel s args => .rel s (args.map (Arg.rename ρ))
    | .eq a b => .eq (ρ a) (ρ b)
    | .lin terms c isEq => .lin (terms.map fun (k, t) => (k, t.rename ρ)) c isEq }

/-- The number of leading variables a literal needs assigned before it can
be evaluated: one more than the largest variable it uses, `0` for none. -/
def Literal.width (l : Literal) : Nat :=
  let argW : Arg → Nat
    | .var v => v + 1
    | .enumConst .. => 0
  match l.atom with
  | .rel _ args => args.foldl (fun w a => max w (argW a)) 0
  | .eq a b => max a b + 1
  | .lin ts _ _ => ts.foldl (fun w (_, t) => t.args.foldl (fun w a => max w (argW a)) w) 0

/-- `∀ vars, ⋁ lits`. An empty disjunction is `False`; a clause with no
variables is a ground disjunction. -/
structure Clause where
  vars : Array SortName
  lits : Array Literal
deriving Repr, BEq, Hashable, Inhabited

namespace Clause

def numLits (c : Clause) : Nat := c.lits.size

/-- Drop the literal at index `i`. The quantifier prefix is kept even when
a variable no longer occurs; a later renaming pass may prune it. -/
def deleteLiteral (c : Clause) (i : Nat) : Clause :=
  { c with lits := c.lits.eraseIdx! i }

/-- Extend a partial substitution `ρ` (indexed by `c`'s variables, `none`
where not yet chosen) so that variable `v` of `c` maps to variable `w` of
`d`: `none` when `v` already maps elsewhere or the sorts differ. -/
private def bindVar (cs ds : Array SortName) (ρ : Array (Option Var)) (v w : Var) : Option (Array (Option Var)) :=
  match ρ[v]? with
  | some (some w') => if w' == w then some ρ else none
  | some none => if cs[v]? == ds[w]? && w < ds.size then some (ρ.set! v (some w)) else none
  | none => none

private def bindArg (cs ds : Array SortName) (ρ : Array (Option Var)) : Arg → Arg → Option (Array (Option Var))
  | .var v, .var w => bindVar cs ds ρ v w
  | a, b => if a == b then some ρ else none

private def bindArgs (cs ds : Array SortName) (ρ : Array (Option Var)) (as bs : Array Arg) : Option (Array (Option Var)) :=
  if as.size != bs.size then none
  else (as.zip bs).foldlM (fun ρ (a, b) => bindArg cs ds ρ a b) ρ

/-- Extend `ρ` so that literal `l` of `c` renames to literal `m` of `d`, the
same test as `l.rename ρ == m`. -/
private def bindLiteral (cs ds : Array SortName) (ρ : Array (Option Var)) (l m : Literal) : Option (Array (Option Var)) :=
  if l.positive != m.positive then none else
  match l.atom, m.atom with
  | .rel s args, .rel s' args' => if s == s' then bindArgs cs ds ρ args args' else none
  | .eq a b, .eq a' b' => (bindVar cs ds ρ a a').bind (bindVar cs ds · b b')
  | .lin ts k e, .lin ts' k' e' =>
    if k != k' || e != e' || ts.size != ts'.size then none
    else (ts.zip ts').foldlM (init := ρ) fun ρ ((i, t), (i', t')) =>
      if i == i' && t.sym == t'.sym then bindArgs cs ds ρ t.args t'.args else none
  | _, _ => none

/-- `c` subsumes `d` when some substitution of `d`'s variables for `c`'s
(respecting sorts, not necessarily injective) maps every literal of `c` to a
literal of `d`. Then `c → d`: `d` is redundant next to `c`. The substitution
is built one literal of `c` at a time, and the literal matched next is the
one with the fewest literals of `d` it can still rename to, so a literal
with none ends the branch at once and a literal whose variables are all
bound is a membership test. The search stops at the first complete match. A
variable of `c` that no literal uses can map to any variable of `d` of its
sort, which must exist. -/
partial def subsumes (c d : Clause) : Bool :=
  c.vars.all d.vars.contains && go (Array.range c.lits.size) (Array.replicate c.vars.size none)
where
  go (todo : Array Nat) (ρ : Array (Option Var)) : Bool := Id.run do
    if todo.isEmpty then return true
    -- The literal with the fewest extensions of `ρ`; stop looking at one.
    let mut best : Option (Nat × Array (Array (Option Var))) := none
    for k in [:todo.size] do
      let exts := d.lits.filterMap (bindLiteral c.vars d.vars ρ c.lits[todo[k]!]! ·)
      if exts.isEmpty then return false
      if best.all (exts.size < ·.2.size) then best := some (k, exts)
      if exts.size == 1 then break
    let some (k, exts) := best | return false
    let rest := todo.eraseIdx! k
    return exts.any (go rest ·)

/-- `c` and `d` subsume each other. -/
def equivalent (c d : Clause) : Bool := c.subsumes d && d.subsumes c

/-- Drop every clause that another clause of the set subsumes (keeping the
first of two equivalent clauses). -/
def removeSubsumed (cs : Array Clause) : Array Clause := Id.run do
  let mut out : Array Clause := #[]
  for i in [:cs.size] do
    let c := cs[i]!
    let redundant := (Array.range cs.size).any fun j =>
      j != i && cs[j]!.subsumes c && (!c.subsumes cs[j]! || j < i)
    unless redundant do out := out.push c
  return out

/-- Variables that occur in some literal. -/
def usedVars (c : Clause) : Array Bool := Id.run do
  let mut used := Array.replicate c.vars.size false
  let mark (used : Array Bool) (v : Var) : Array Bool :=
    if v < used.size then used.set! v true else used
  for l in c.lits do
    match l.atom with
    | .rel _ args =>
      for a in args do
        if let .var v := a then used := mark used v
    | .eq a b => used := mark (mark used a) b
    | .lin terms _ _ =>
      for (_, t) in terms do
        for a in t.args do
          if let .var v := a then used := mark used v
  return used

/-- Remove unused quantified variables, renumbering the rest. -/
def pruneVars (c : Clause) : Clause := Id.run do
  let used := c.usedVars
  let mut remap : Array (Option Nat) := #[]
  let mut vars : Array SortName := #[]
  for i in [:c.vars.size] do
    if used[i]! then
      remap := remap.push (some vars.size)
      vars := vars.push c.vars[i]!
    else
      remap := remap.push none
  let ren (v : Var) : Var := (remap[v]!).getD 0
  return { vars, lits := c.lits.map (Literal.rename ren) }

end Clause

/-! ## Finite structures -/

/-- A finite first-order structure: a domain size per sort, and per symbol the
tuples (as element indices) on which it holds; a function symbol's table holds
its graph, rows `args ++ [value]`, one per argument tuple. Elements of sort
`s` are `0 .. size s - 1`. An enum sort's size is its number of constructors
and its element `i` is constructor `i`. -/
structure FinStructure where
  sorts : Array (SortName × Nat)
  /-- The enum sorts among `sorts`, each with its constructor names in order. -/
  enums : Array (SortName × Array Name) := #[]
  rels : Array (RelSym × Array (Array Nat))
  /-- Numeric-valued symbols (`individual x : Int`, `function f : node → Nat`)
  with the value of every argument tuple, arguments as element indices. -/
  nums : Array (RelSym × Array (Array Nat × Int)) := #[]
deriving Repr, BEq, Inhabited

namespace FinStructure

def sortSize (m : FinStructure) (s : SortName) : Nat :=
  ((m.sorts.find? (·.1 == s)).map (·.2)).getD 0

def isEnum (m : FinStructure) (s : SortName) : Bool := m.enums.any (·.1 == s)

/-- The constructor name of element `i` of an enum sort. -/
def enumCtor? (m : FinStructure) (s : SortName) (i : Nat) : Option Name :=
  (m.enums.find? (·.1 == s)).bind fun (_, ctors) => ctors[i]?

/-- Element `i` of sort `s` for display: its constructor name for an enum
sort, its index otherwise. -/
def elementName (m : FinStructure) (s : SortName) (i : Nat) : String :=
  match m.enumCtor? s i with
  | some c => c.toString
  | none => toString i

def holds (m : FinStructure) (sym : RelSym) (tuple : Array Nat) : Bool :=
  match m.rels.find? (·.1 == sym) with
  | some (_, tuples) => tuples.contains tuple
  | none => false

/-- All tuples of element indices for the given argument sorts. -/
def tuples (m : FinStructure) (argSorts : Array SortName) : Array (Array Nat) :=
  argSorts.foldl (init := #[#[]]) fun acc s =>
    acc.flatMap fun t => (Array.range (m.sortSize s)).map (t.push ·)

/-- Elements of the uninterpreted sorts as (sort, index) pairs, in a fixed
order. This order is the variable order of `diagram`. Enum elements are not
listed: a diagram names them as constants instead of quantifying over them. -/
def elements (m : FinStructure) : Array (SortName × Nat) :=
  (m.sorts.filter fun (s, _) => !m.isEnum s).flatMap fun (s, n) => (Array.range n).map (s, ·)

/-- Every numeric term of the structure with its value: for each numeric
symbol and each row of its table, the symbol applied to the row's arguments
(as clause arguments through `argOf`). -/
def numTerms (m : FinStructure) (argOf : SortName → Nat → Arg) : Array (NumTerm × Int) :=
  m.nums.flatMap fun (sym, table) =>
    table.map fun (row, v) =>
      (⟨sym, (sym.argSorts.pop.zip row).map fun (s, i) => argOf s i⟩, v)

/-- The value of a numeric term under an assignment of variables to elements. -/
def numValue (m : FinStructure) (asg : Array Nat) (t : NumTerm) : Option Int := do
  let (_, table) ← m.nums.find? (·.1 == t.sym)
  let el : Arg → Nat
    | .var v => asg[v]!
    | .enumConst _ i => i
  let row := t.args.map el
  (table.find? (·.1 == row)).map (·.2)

/-- The diagram of `m` (Karbyshev et al. 2017, Def. 4.1): an existential
sentence true in exactly the structures containing an isomorphic copy of `m`
as a substructure (Lemma 4.3). We return its body as literals over
variables `0 .. |elements|-1`, one per element of an uninterpreted sort; the
caller decides whether to read it existentially (the diagram) or negate it
into a universal clause (the blocking clause). Literals: every atomic fact of
every relation and every constant, positive or negative; for every function
symbol with arguments one positive literal per row of its graph (the negative
facts follow, see the module header); and `x ≠ y` for distinct elements of the
same uninterpreted sort. An element of an enum sort appears as its
constructor. -/
def diagramLiterals (m : FinStructure) : Array Literal := Id.run do
  let els := m.elements
  let argOf (s : SortName) (i : Nat) : Arg :=
    match m.enumCtor? s i with
    | some ctor => .enumConst ctor i
    | none =>
      match els.findIdx? (fun (s', i') => s' == s && i' == i) with
      | some v => .var v
      -- `decodeTrace` rejects an index outside the sort, so this is unreachable
      -- for a decoded structure; a hand-built one with a bad index fails loudly.
      | none => panic! s!"IC3: element {i} of sort {s} is not an element of the structure"
  let mut lits : Array Literal := #[]
  for (sym, table) in m.rels do
    let argsOf (t : Array Nat) : Array Arg := (sym.argSorts.zip t).map fun (s, i) => argOf s i
    if sym.isFunction && sym.argSorts.size > 1 then
      for row in table do
        lits := lits.push { positive := true, atom := .rel sym (argsOf row) }
    else
      for t in m.tuples sym.argSorts do
        lits := lits.push { positive := m.holds sym t, atom := .rel sym (argsOf t) }
  for i in [:els.size] do
    for j in [i+1:els.size] do
      if els[i]!.1 == els[j]!.1 then
        lits := lits.push { positive := false, atom := .eq i j }
  -- Numeric terms: the value of every term as a numeral literal, and the
  -- order between the terms of one sort: sorted by value, consecutive terms
  -- are related by `<` or, when their values agree, by `=`. The order
  -- literals entail every pairwise order and distinctness, so no `≠` is added.
  let terms := m.numTerms argOf
  for (t, v) in terms do
    lits := lits.push { positive := true, atom := .numEq t v }
  let sorts := (terms.map (·.1.sort)).foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]
  for s in sorts do
    let ts := (terms.filter (·.1.sort == s)).qsort fun a b => a.2 < b.2
    for i in [1:ts.size] do
      let (t₁, v₁) := ts[i-1]!
      let (t₂, v₂) := ts[i]!
      let a : Atom := if v₁ == v₂ then Atom.numEqOffset t₁ t₂ 0 else Atom.numLt t₁ t₂
      lits := lits.push { positive := true, atom := a }
  return lits

/-- The blocking clause `¬ Diag(m)`: `∀ x̄, ⋁ ¬ℓ` over the diagram's literals.
It excludes exactly the states that contain `m` as a substructure. -/
def negatedDiagram (m : FinStructure) : Clause :=
  { vars := m.elements.map (·.1), lits := m.diagramLiterals.map Literal.negate }

/-- Evaluate a literal under an assignment of variables to elements: `none`
when the structure does not determine it, that is when it lacks the
literal's relation symbol, or a numeric symbol or a row of its table that a
linear term needs. Decoded structures are total over the signature
(`Vocabulary.lean`), so this arises only for a hand-built structure. -/
def evalLiteral (m : FinStructure) (asg : Array Nat) (l : Literal) : Option Bool := do
  let el : Arg → Nat
    | .var v => asg[v]!
    | .enumConst _ i => i
  let v ← match l.atom with
    | .rel sym args => (m.rels.find? (·.1 == sym)).map fun (_, tuples) => tuples.contains (args.map el)
    | .eq a b => some (asg[a]! == asg[b]!)
    | .lin terms c isEq =>
      (terms.foldlM (init := c) fun acc (k, t) => (m.numValue asg t).map (acc + k * ·)).map fun sum =>
        if isEq then sum == 0 else sum ≤ 0
  return if l.positive then v else !v

/-- Search the assignments of `vars` to elements of their sorts one variable
at a time, variable `i` after variables `0 … i-1`. At each step `decided`
looks at the literals that have just become evaluable (width `i`) and may
settle the whole subtree (`some b`); a complete assignment no step settled
is `atLeaf`. `universal` asks whether the subtrees all answer `true`, otherwise
whether one does; the search stops at the first subtree that decides. -/
private partial def searchAssignments (m : FinStructure) (vars : Array SortName) (lits : Array Literal)
    (decided : Array Nat → Array Literal → Option Bool) (atLeaf : Bool) (universal : Bool) : Bool :=
  let byWidth : Array (Array Literal) := lits.foldl (init := Array.replicate (vars.size + 1) #[]) fun acc l =>
    acc.modify (min l.width vars.size) (·.push l)
  let rec go (i : Nat) (asg : Array Nat) : Bool :=
    match decided asg byWidth[i]! with
    | some b => b
    | none =>
      if i ≥ vars.size then atLeaf
      else
        let els := Array.range (m.sortSize vars[i]!)
        if universal then els.all (go (i + 1) <| asg.push ·) else els.any (go (i + 1) <| asg.push ·)
  go 0 #[]

/-- `m ⊨ c` for a universal clause `c`: every assignment satisfies some
literal. A literal the structure does not determine counts as satisfied: the
callers use a `false` answer to reject a clause (a candidate false in a
reachable state is not an invariant), and a structure that lacks a value is
no ground for rejecting anything. The assignments are enumerated one variable
at a time: a partial assignment that already makes a literal true satisfies
every extension and is not extended, and the first assignment that makes
every literal false ends the search. -/
def models (m : FinStructure) (c : Clause) : Bool :=
  searchAssignments m c.vars c.lits (atLeaf := false) (universal := true) fun asg ls =>
    if ls.any fun l => (m.evalLiteral asg l).getD true then some true else none

/-- `m ⊨ ∃ x̄, ⋀ lits`: some assignment satisfies every literal, a literal
the structure does not determine counted as unsatisfied. Enumerated like
`models`: a partial assignment that makes a literal false is not extended. -/
def modelsExistential (m : FinStructure) (vars : Array SortName) (lits : Array Literal) : Bool :=
  searchAssignments m vars lits (atLeaf := true) (universal := false) fun asg ls =>
    if ls.any fun l => !((m.evalLiteral asg l).getD false) then some false else none

end FinStructure
end Veil.Synthesizer
