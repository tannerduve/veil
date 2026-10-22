module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Query
public meta import Veil.Core.Tools.Synthesizer.Vocabulary
public meta import Veil.Core.Tools.Synthesizer.Certificate
public import Veil.Core.Tools.Synthesizer.Soundness

/-!
# The counterexample certificate

When the search finds an execution that violates the property, the solver's
model is decoded into finite structures: each uninterpreted sort is a set
`Fin n`, each enum sort its concrete type (`Mod.roleT_IndT`, the inductive
Veil declares for it), each relation a table of tuples, each function a table
of rows. This file turns that execution into a theorem in the module's
namespace:

    theorem Mod.ic3_unsafe : ¬ (∀ th st,
      (Mod.relationalTransitionSystem (Fin n₁) …).reachable th st → Mod.ic3_prop (Fin n₁) … th st)

The statement says: at these sort sizes, with these typeclass instances, the
property does not hold of every reachable state. It is the negation of what
`ic3_safe` would state for the same instantiation.

The proof is assembled from definitions the file emits:

1. `ic3_cex_th`, the theory (immutable components) as a structure literal
   whose relation fields are `fun x … => decide (x = a ∧ … ∨ …)` over the
   model's tables and whose function fields are `fun x … => if x = a ∧ …
   then b else …` over the rows; `ic3_cex_s0 … ic3_cex_sk`, the states, in
   the same form. An element of an enum sort is written as its constructor.
2. For every instantiated typeclass, an instance at the concrete sorts whose
   relation, constant and function fields come from the model and whose
   axiom fields are proven by `decide` (the sorts are finite). The
   transition system and `ic3_prop` receive each instance by the name of its
   binder (`(tot := ic3_cex_inst_tot)`), not through instance resolution:
   two instances of one class at sorts of the same size are both instances
   at `Fin n`. The class of an enum sort needs no instance of ours: Veil
   declares one at the concrete type when the enum is declared, and instance
   resolution finds it.
3. One theorem per fact the path needs: the theory satisfies the module's
   assumptions, the first state is initial, each step is a transition of the
   labeled action, and the last state violates `ic3_prop`. Each is proven by
   unfolding the module's definitions, running Veil's `nextSimp` simp set, and
   finishing with `simp` or `decide` on the concrete values.
4. `ic3_unsafe` applies `Veil.Synthesizer.unsafe_of_path` to those facts.

Everything is checked by the kernel before the command finishes; nothing
depends on the solver, and `#print axioms Mod.ic3_unsafe` lists the three
standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

The transition system is Veil's `relationalTransitionSystem`, whose initial
states run `after_init` from the default state and which does not assume
`trusted invariant`s; see `Certificate.lean`.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil Lean.Parser.Term

/-- `(k : Fin n)`. -/
private def finTerm (n k : Nat) : Term :=
  Unhygienic.run `(term| (($(Syntax.mkNumLit (toString k)) : Fin $(Syntax.mkNumLit (toString n)))))

/-- What the certificate is built from: the module, its vocabulary and the
decoded execution. -/
structure CexCtx where
  mod : Veil.Module
  sig : Signature
  path : DecodedTrace

namespace CexCtx

/-- The size of a sort in the decoded execution. -/
def sortSize (c : CexCtx) (s : SortName) : CommandElabM Nat := do
  match c.path.sorts.find? (·.1 == s) with
  | some (_, n) => if n == 0 then throwError "IC3: sort {s} has size 0 in the model" else pure n
  | none => throwError "IC3: the model does not instantiate sort {s}"

/-- The constructors of an enum sort, if `s` is one. -/
def enumCtors? (c : CexCtx) (s : SortName) : Option (Array Name) :=
  (c.sig.enums.find? (·.1 == s)).map (·.2)

/-- The type a sort is instantiated at: `Fin n` for an uninterpreted sort of
size `n`, the concrete enum type for an enum sort. -/
def sortTerm (c : CexCtx) (s : SortName) : CommandElabM Term := do
  if (c.enumCtors? s).isSome then
    return mkIdent (c.mod.name ++ Name.toEnumConcreteTypeName s)
  let n ← c.sortSize s
  return Unhygienic.run `(term| Fin $(Syntax.mkNumLit (toString n)))

/-- Element `k` of sort `s` as a term: `(k : Fin n)`, or constructor `k` of
the enum. -/
def valueTerm (c : CexCtx) (s : SortName) (k : Nat) : CommandElabM Term := do
  match c.enumCtors? s with
  | some ctors =>
    let some ctor := ctors[k]? | throwError "IC3: enum sort {s} has no constructor at index {k}"
    return mkIdent (c.mod.name ++ Name.toEnumConcreteTypeName s ++ ctor.updatePrefix .anonymous)
  | none =>
    let n ← c.sortSize s
    -- `(k : Fin n)` would reduce modulo `n` and hide a bad index.
    unless k < n do throwError "IC3: element {k} of sort {s} is out of range; the model has {n} element(s)"
    return finTerm n k

/-- Argument binder names `a0 a1 …`. -/
def argIdents (n : Nat) : Array Term := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"a{i}")

/-- The value of a relation symbol as a Lean term over the concrete sorts: a
function of the arguments whose body is the disjunction over the table's rows
of "argument equals row entry" conjunctions. `Prop`-valued unless `asBool`; a
0-ary relation is the proposition or boolean itself. -/
def tableTerm (c : CexCtx) (argSorts : Array SortName) (rows : Array (Array Nat))
    (asBool : Bool) : CommandElabM Term := do
  let vars := argIdents argSorts.size
  let rowTerms : Array Term ← rows.mapM fun row => do
    let eqs : Array Term ← (Array.range row.size).mapM fun i => do
      `(term| $(vars[i]!) = $(← c.valueTerm argSorts[i]! row[i]!))
    if eqs.isEmpty then `(term| True) else repeatedAnd eqs
  let body : Term ← if rowTerms.isEmpty then `(term| False) else repeatedOr rowTerms
  let body : Term ← if asBool then `(term| decide $body) else pure body
  if vars.isEmpty then return body
  let binders ← (Array.range vars.size).mapM fun i => do
    `(funBinder| ($(vars[i]!) : $(← c.sortTerm argSorts[i]!)))
  `(term| fun $binders* => $body)

/-- The value of a function symbol as a Lean term: a function of the
arguments that tests the rows in turn, `if a0 = x ∧ … then v else …`, the
last row's value being the final branch (the table is total). A 0-ary
function is its value. -/
def functionTerm (c : CexCtx) (argSorts : Array SortName) (result : SortName) (rows : Array (Array Nat))
    : CommandElabM Term := do
  let valueOf (row : Array Nat) : CommandElabM Term := c.valueTerm result (row.back?.getD 0)
  let fallback : CommandElabM Term := match rows.back? with
    | some row => valueOf row
    | none => `(term| default)
  if argSorts.isEmpty then return ← fallback
  let vars := argIdents argSorts.size
  let mut body : Term ← fallback
  for row in rows.pop.reverse do
    let eqs : Array Term ← (Array.range argSorts.size).mapM fun i => do
      `(term| $(vars[i]!) = $(← c.valueTerm argSorts[i]! row[i]!))
    let cond ← repeatedAnd eqs
    let v ← valueOf row
    body ← `(term| if $cond then $v else $body)
  let binders ← (Array.range vars.size).mapM fun i => do
    `(funBinder| ($(vars[i]!) : $(← c.sortTerm argSorts[i]!)))
  `(term| fun $binders* => $body)

/-- The value of a numeric-valued symbol: the integer literal of an
`individual`, or a function of the arguments testing the rows in turn with
integer literals as values (the table is total; the last row is the final
branch). -/
def numFunctionTerm (c : CexCtx) (argSorts : Array SortName) (result : SortName)
    (rows : Array (Array Nat × Int)) : CommandElabM Term := do
  let valueOf (row : Array Nat × Int) : CommandElabM Term := numeralTerm result row.2
  let fallback : CommandElabM Term := match rows.back? with
    | some row => valueOf row
    | none => numeralTerm result 0
  if argSorts.isEmpty then return ← fallback
  let vars := argIdents argSorts.size
  let mut body : Term ← fallback
  for row in rows.pop.reverse do
    let eqs : Array Term ← (Array.range argSorts.size).mapM fun i => do
      `(term| $(vars[i]!) = $(← c.valueTerm argSorts[i]! row.1[i]!))
    let cond ← repeatedAnd eqs
    let v ← valueOf row
    body ← `(term| if $cond then $v else $body)
  let binders ← (Array.range vars.size).mapM fun i => do
    `(funBinder| ($(vars[i]!) : $(← c.sortTerm argSorts[i]!)))
  `(term| fun $binders* => $body)

/-- The value of a module component (state or theory) in a structure. Veil
stores relations and `Bool` individuals as `Bool`-valued fields, sort-valued
individuals as elements, functions as functions and integer components as
integers. -/
def componentValue (c : CexCtx) (σ : FinStructure) (sym : RelSym) : CommandElabM Term := do
  if sym.isNumeric then
    let rows := (σ.nums.find? (·.1.key == sym.key)).map (·.2) |>.getD #[]
    let some result := sym.argSorts.back? | throwError "IC3: {sym.name} without a result sort"
    return ← c.numFunctionTerm sym.argSorts.pop result rows
  let rows := (σ.rels.find? (·.1.key == sym.key)).map (·.2) |>.getD #[]
  match sym.source with
  | .state => c.tableTerm sym.argSorts rows true
  | .boolIndividual => pure (if rows.isEmpty then Unhygienic.run `(term| false) else Unhygienic.run `(term| true))
  | .individualEq =>
    let some sName := sym.argSorts[0]? | throwError "IC3: individual {sym.name} without a sort"
    c.valueTerm sName ((rows[0]?.bind (·[0]?)).getD 0)
  | .function =>
    let some result := sym.argSorts.back? | throwError "IC3: function {sym.name} without a result sort"
    c.functionTerm sym.argSorts.pop result rows
  | _ => throwError "IC3: {sym.key} is not a module component"

end CexCtx

/-- `{ f₁ := v₁, … }` structure-instance syntax. -/
private def structInstance (fields : Array (Name × Term)) : CommandElabM Term := do
  let items ← fields.mapM fun (f, v) => `(structInstField| $(mkIdent f):ident := $v)
  `(term| { $items:structInstField,* })

/-- The action name and its argument values from a decoded transition label
(`{"recv": {"sender": 0, "n": 1}}`; an enum-typed argument arrives as its
constructor name, a `Bool` one as a boolean, an integer one as a number, an
element of an uninterpreted sort as its index). -/
private def labelTerm (c : CexCtx) (j : Json) : CommandElabM Term := do
  let mod := c.mod
  let (actName, args) ← match j with
    | .obj kvs => match kvs.toArray with
      | #[(k, v)] => pure (Name.mkSimple k, v)
      | _ => throwError "IC3: unexpected transition label {j}"
    | .str k => pure (Name.mkSimple k, Json.obj {})
    | _ => throwError "IC3: unexpected transition label {j}"
  let some act := mod.actions.find? (·.name == actName)
    | throwError "IC3: transition label names unknown action {actName}"
  let (_, params) ← liftTermElabM (mod.declarationAllParams act.name act.declarationKind)
  let argTerms : Array Term ← params.mapM fun p => do
    let v := (args.getObjVal? p.name.toString).toOption
    match p.type.raw with
    | .ident _ _ sName _ =>
      if sName == ``Bool then
        match v with
        | some (.bool b) => pure (if b then Unhygienic.run `(term| true) else Unhygienic.run `(term| false))
        | _ => throwError "IC3: label argument {p.name} of action {actName} has no Bool value"
      else if let some ctors := c.enumCtors? sName then
        match v with
        | some (.str ctor) =>
          let some k := ctors.findIdx? (·.ctorBase == ctor)
            | throwError "IC3: label argument {p.name} of action {actName} names no constructor of {sName}: {ctor}"
          c.valueTerm sName k
        | _ => throwError "IC3: label argument {p.name} of action {actName} has no value in the model"
      else if isNumericSort sName then
        match v with
        | some (.num k) =>
          unless k.exponent == 0 do
            throwError "IC3: label argument {p.name} of action {actName} is not an integer: {k}"
          if sName == `Nat && k.mantissa < 0 then
            throwError "IC3: label argument {p.name} of action {actName} is negative for a Nat parameter: {k}"
          numeralTerm sName k.mantissa
        | _ => throwError "IC3: label argument {p.name} of action {actName} has no value in the model"
      else
        match v with
        | some (.num k) => c.valueTerm sName k.mantissa.toNat
        | _ => throwError "IC3: label argument {p.name} of action {actName} has no value in the model"
    | _ => throwError "IC3: action {actName} has a parameter of unsupported type {p.type}"
  let ctor := mkIdent (labelTypeName ++ act.name)
  if argTerms.isEmpty then pure ctor else `(term| $ctor $argTerms*)

/-- Split every variable of an enumeration type (an inductive type whose
constructors take no arguments, such as the concrete type `s_IndT` of an enum
sort) into its constructors. A Veil action decides equality at an enum sort
through the enum's class, which neither `decide` nor `simp` evaluates while
the compared value is a variable; once every such variable is a constructor,
`simp` evaluates each comparison. -/
elab "veil_enum_cases" : tactic => do
  let rec split : MVarId → Nat → MetaM (List MVarId)
  | g, 0 => pure [g]
  | g, fuel + 1 => g.withContext do
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let .const n _ := (← whnf d.type).getAppFn | continue
      let some (.inductInfo info) := (← getEnv).find? n | continue
      unless info.numParams == 0 && info.numIndices == 0 && info.ctors.length > 1 do continue
      let nullary ← info.ctors.allM fun ctor => do
        match (← getEnv).find? ctor with
        | some (.ctorInfo ci) => pure (ci.numFields == 0)
        | _ => pure false
      unless nullary do continue
      let cases ← g.cases d.fvarId
      return (← cases.toList.mapM fun sub => split sub.mvarId fuel).flatten
    return [g]
  Lean.Elab.Tactic.liftMetaTactic fun g => split g 64

/-- The tactic that proves a concrete fact about the module's definitions:
unfold, normalize with Veil's simp set, then evaluate on the finite values. -/
private def concreteTactic (unfoldNames : Array Ident) (valueDefs : Array Ident) : CommandElabM (TSyntax `tactic) := do
  let nextSimp := mkIdent `nextSimp
  `(tactic| (
      unfold $[$unfoldNames:ident]*
      try veil_simp +$(mkIdent `instances) only [$nextSimp:ident]
      all_goals first
        | decide
        | (simp +$(mkIdent `instances) only [$[$valueDefs:ident],*]; done)
        | (simp +$(mkIdent `instances) [$[$valueDefs:ident],*]; done)
        | (simp +$(mkIdent `instances) only [$[$valueDefs:ident],*]; decide)
        | (simp +$(mkIdent `instances) [$[$valueDefs:ident],*]; decide)
        | (simp +$(mkIdent `instances) [$[$valueDefs:ident],*]; intros; veil_enum_cases <;> simp_all +$(mkIdent `instances) [$[$valueDefs:ident],*]; done)
        | (refine ⟨?_, ?_⟩ <;> first | decide | (simp +$(mkIdent `instances) [$[$valueDefs:ident],*]; done) | (funext; decide))))

/-- Build and check the counterexample certificate. `property` are the
conjuncts of `P` as the controller used them. -/
def certifyUnsafe (mod : Veil.Module) (property : Array Term) (path : DecodedTrace)
    : CommandElabM CertificateResult := do
  if path.states.isEmpty then throwError "IC3: empty counterexample"
  throwIfCertified mod [`ic3_unsafe, `ic3_prop]
  let ctx ← liftTermElabM (QueryCtx.ofModule mod)
  let sig ← liftTermElabM (Signature.ofModule mod)
  let c : CexCtx := { mod, sig, path }
  let sortTerms : Array Term ← sig.sorts.mapM c.sortTerm
  let modName (n : Name) : Ident := mkIdent (mod.name ++ n)
  -- 1. Typeclass instances at the concrete sorts.
  let mut instNames : Array Ident := #[]
  let mut instArgs : Array (TSyntax ``namedArgument) := #[]
  for (inst, className, sortArgs) in sig.typeclassInsts do
    let specs ← liftTermElabM (Signature.classFieldSpecs inst className sortArgs)
    let σ := path.states[0]!
    let mut fields : Array (Name × Term) := #[]
    for (field, spec) in specs do
      let key := (inst ++ field).toString
      let rows := (σ.rels.find? (·.1.key.toString == key)).map (·.2) |>.getD #[]
      match spec with
      | .relation argSorts isBool => fields := fields.push (field, ← c.tableTerm argSorts rows isBool)
      | .const sName => fields := fields.push (field, ← c.valueTerm sName ((rows[0]?.bind (·[0]?)).getD 0))
      | .function argSorts result => fields := fields.push (field, ← c.functionTerm argSorts result rows)
      | .axiom _ => fields := fields.push (field, ← `(term| by first | decide | (intros; simp_all; done) | (intros; grind)))
      | .other => throwError "IC3: field {field} of {className} is neither a relation, a constant, a function between sorts nor an axiom; the counterexample certificate cannot build the instance"
    let instName := mkIdent (Name.mkSimple s!"ic3_cex_inst_{inst}")
    let classArgs : Array Term ← sortArgs.mapM c.sortTerm
    let value ← structInstance fields
    elabChecked (← `(command| instance (priority := high) $instName:ident : $(mkIdent className) $classArgs* := $value))
    instNames := instNames.push instName
    instArgs := instArgs.push (← `(namedArgument| ($(mkIdent inst) := $instName)))
  -- 2. Theory and states.
  let theoryT ← `(term| @$(mkIdent theoryName) $sortTerms*)
  let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sortTerms*))
  let thName := mkIdent `ic3_cex_th
  let thFields ← sig.immutableComponents.mapM fun sym => do pure (sym.name, ← c.componentValue path.states[0]! sym)
  elabChecked (← `(command| def $thName : $theoryT := $(← structInstance thFields)))
  let stateNames := (Array.range path.states.size).map fun i => mkIdent (Name.mkSimple s!"ic3_cex_s{i}")
  for i in [:path.states.size] do
    let fields ← sig.stateRels.mapM fun sym => do pure (sym.name, ← c.componentValue path.states[i]! sym)
    elabChecked (← `(command| def $(stateNames[i]!) : $stateT := $(← structInstance fields)))
  -- 3. `ic3_prop` and the per-fact theorems.
  let propName := mkIdent `ic3_prop
  definePredicate ctx propName property
  -- Each instance is passed by its binder name: two instances of one class
  -- at sorts of the same size are both instances of `C (Fin n)`, and instance
  -- resolution would pick the same one for both.
  -- (A `namedArgument` is an argument of an application like a term; the
  -- splice below takes terms.)
  let instArgTerms : Array Term := instArgs.map (⟨·.raw⟩)
  let rts ← `(term| $(mkIdent assembledRTSName) $sortTerms* $instArgTerms*)
  let prop ← `(term| $propName $sortTerms* $instArgTerms*)
  let rtsName := modName assembledRTSName
  -- What the concrete proofs unfold: the theory, the states, and the
  -- instances built above, so that a class projection in a guard
  -- (`tot.le zero n`) reduces to its `fun` body, which `decide` can
  -- evaluate; a projection of a named instance is opaque to `simp` and to
  -- instance resolution.
  -- An enum constant inside an action is the enum class's field
  -- (`s_EnumClass.c`), and `simp` does not unfold it to the constructor of
  -- the concrete type; `rfl` proves the equation it needs.
  let mut enumEqs : Array Ident := #[]
  for (s, ctors) in sig.enums do
    for ctor in ctors do
      let base := ctor.updatePrefix .anonymous
      let eqName := mkIdent (Name.mkSimple s!"ic3_cex_enum_{s}_{base}")
      elabChecked (← `(command| theorem $eqName :
          ($(mkIdent (Name.toEnumClass s ++ base)) : $(← c.sortTerm s)) = $(← c.valueTerm s (ctors.idxOf ctor)) := rfl))
      enumEqs := enumEqs.push eqName
  let valueDefs := #[thName] ++ stateNames ++ instNames ++ enumEqs
  let hasName := mkIdent `ic3_cex_assumptions
  elabChecked (← `(command| theorem $hasName : ($rts).$(mkIdent `assumptions) $thName := by
    $(← concreteTactic #[rtsName, modName `Assumptions] valueDefs):tactic))
  let initName := mkIdent `ic3_cex_init
  elabChecked (← `(command| theorem $initName : ($rts).$(mkIdent `init) $thName $(stateNames[0]!) := by
    $(← concreteTactic #[rtsName, modName `Init] valueDefs):tactic))
  let mut stepNames : Array Ident := #[]
  let mut stepPairs : Array Term := #[]
  for i in [1:path.states.size] do
    let lbl ← labelTerm c path.labels[i]!
    let stepName := mkIdent (Name.mkSimple s!"ic3_cex_step_{i - 1}")
    elabChecked (← `(command| theorem $stepName :
        ($rts).$(mkIdent `tr) $thName $(stateNames[i - 1]!) $lbl $(stateNames[i]!) := by
      $(← concreteTactic #[rtsName, modName `Next] valueDefs):tactic))
    stepNames := stepNames.push stepName
    stepPairs := stepPairs.push (← `(term| ($lbl, $(stateNames[i]!))))
  let lastState := stateNames.back!
  let badName := mkIdent `ic3_cex_bad
  elabChecked (← `(command| theorem $badName : ¬ ($prop) $thName $lastState := by
    $(← concreteTactic #[propName] valueDefs):tactic))
  -- 4. The theorem.
  let th := mkIdent `th
  let st := mkIdent `st
  let validProof : Term ← match stepNames.size with
    | 0 => `(term| (by simp only [Veil.Synthesizer.pathValid]))
    | 1 => `(term| (by simp only [Veil.Synthesizer.pathValid, and_true]; exact $(stepNames[0]!)))
    | _ => `(term| (by simp only [Veil.Synthesizer.pathValid, and_true]; exact ⟨$[$stepNames:ident],*⟩))
  let thmName := mkIdent `ic3_unsafe
  elabChecked (← `(command|
    theorem $thmName : ¬ (∀ ($th : $theoryT) ($st : $stateT),
        ($rts).$(mkIdent `reachable) $th $st → ($prop) $th $st) :=
      Veil.Synthesizer.unsafe_of_path ($rts) ($prop) $thName $(stateNames[0]!) [$stepPairs,*]
        $hasName $initName $validProof (by simp only [Veil.Synthesizer.pathLast]; exact $badName)))
  liftCoreM <| certificateResult (mod.name ++ thmName.getId) (mod.name ++ propName.getId)

end Veil.Synthesizer
