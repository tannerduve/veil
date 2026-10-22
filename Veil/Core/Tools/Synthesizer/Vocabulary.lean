module

public meta import Veil
public meta import Veil.Core.UI.Verifier.TraceCounterexample
public meta import Veil.Core.Tools.Synthesizer.Clause

/-!
# The vocabulary of a module, and reading solver models as finite structures

This module has two halves. The first decides the *vocabulary*: the symbols an
invariant may mention, which is also what the "no universal invariant" verdict
(Proposition 5.6 of the paper) is relative to. `Signature.ofModule` collects
mutable and immutable components from `mod.signature` (relations,
individuals and functions), the constructors of every enum sort, and the
relations, sort-valued constants and sort-valued functions of every
instantiated typeclass from the class declarations. Leaving a symbol out of
the vocabulary would make that verdict wrong, so an unsupported component
shape is an error. The only symbols left out are class fields whose result
type is outside the class's sort parameters (and `Prop`, `Bool`), an
`Int`-valued field for example; the vocabulary is defined without them, they
are listed in `Signature.excludedClassFields` so the verdict message can name
them, and they are reported under `set_option trace.veil.synthesizer.debug true`. Ghost
definitions (`ghost relation`,
`ghost function`) are not symbols: the queries see their bodies, so a clause
over one is a clause over the vocabulary only when the body is
quantifier-free. `Signature.ghosts` names them so the verdict message can say
so.

An enum sort (`enum roleT = {leader, follower}`) is, to Veil, a sort
parameter together with a class `roleT_EnumClass` whose constant fields are
the constructors and whose axioms say they are distinct and exhaustive,
instantiated as `roleT_Enum`. Here the constructors become `Arg.enumConst`
arguments of atoms and the class is not listed among the typeclass symbols:
its constants are already in the vocabulary as constructors, and its axioms
are part of every query through the instance binder Veil adds.

The second half reads solver models as finite structures. Veil decodes an SMT
model of a trace query into a `VeilTrace` and renders it as JSON
(`VeilTrace.toJson`): sort sizes under `instantiation` (`"node": "Fin 2"`; an
enum sort is instantiated at its concrete type, `"roleT": "roleT_IndT"`),
per-state component tables under `states[i].fields` (a relation of arity `k`
is a list of `k`-tuples, a unary one a flat list, a `Bool` individual a
boolean, a function a list of rows `[args, value]` where `args` is the
argument tuple, left-nested for two or more arguments (`[[a₁, a₂], value]`),
a sort-valued individual a bare value), and the instantiated typeclass
symbols under
`extraVals` (`"tot.le": [[0,0],[0,1],[1,1]]`, already converted from `Prop`
to `Bool`). An element of an enum sort arrives as its constructor name
(`"leader"`). Immutable components arrive under `theory`. `decodeTrace`
turns that JSON into `FinStructure`s.

Veil's module representation is read here, in `Query.lean` (query assembly
and the solver pipeline), in `Controller.lean` and `Command.lean` (the safety,
invariant and trusted-invariant lists, `uqc%`) and in `Certificate.lean` /
`Counterexample.lean` (Veil's generated names for the transition system,
labels and action tags).
-/

public meta section

initialize Lean.registerTraceClass `veil.synthesizer.debug

namespace Veil.Synthesizer
open Lean Elab Meta Veil

/-- The relation vocabulary of a module, as UPDR sees it. -/
structure Signature where
  /-- Sort parameters, in declaration order, enum sorts included. -/
  sorts : Array SortName
  /-- The enum sorts among `sorts`, each with its constructor names in
  declaration order. -/
  enums : Array (SortName × Array Name) := #[]
  /-- Mutable relations and individuals of the state. -/
  stateRels : Array RelSym
  /-- Immutable relations and individuals; Veil stores them in the module's `Theory`. -/
  immutableComponents : Array RelSym
  /-- Relations and constants of the instantiated typeclasses (`tot.le`, `tot.zero`). -/
  classSymbols : Array RelSym
  /-- Instantiated typeclasses: instance name, class name, sort arguments. -/
  typeclassInsts : Array (Name × Name × Array SortName) := #[]
  /-- Class symbols (by `RelSym.key`) that no axiom of their class mentions.
  A model may leave such a symbol out, and `defaultTable` completes it; a
  missing symbol outside this list is a decoding error. -/
  freeClassSymbols : Array Name := #[]
  /-- The module's ghost definitions (`ghost relation`, `ghost function` and
  their `theory` variants), by name. They are not symbols of the vocabulary:
  queries see their bodies. -/
  ghosts : Array Name := #[]
  /-- Class fields left out of the vocabulary (`inst.field`), because their
  result type is outside the module's sorts, `Prop` and `Bool`
  (`FieldSpec.other`). The verdict message names them. -/
  excludedClassFields : Array Name := #[]
  /-- The numeric sorts (`Int`, `Nat`) that are the result of some component. -/
  numericSorts : Array SortName := #[]
  /-- The integer literals written in the module's actions and properties, with
  `0` and `1`: the constants the linear templates use. -/
  numerals : Array Int := #[]
deriving Repr, Inhabited

/-- What a field of a typeclass is, for the symbols it contributes and for
building a concrete instance at `Fin n`. -/
inductive FieldSpec where
  /-- A predicate over the class's sort parameters, `Prop`- or `Bool`-valued. -/
  | relation (argSorts : Array SortName) (isBool : Bool)
  /-- A constant of one of the sorts. -/
  | const (sort : SortName)
  /-- A function from the class's sort parameters into one of them. -/
  | function (argSorts : Array SortName) (result : SortName)
  /-- A proposition about the other fields (`le_refl`), proven when an
  instance is built; `mentions` lists the fields its statement uses. -/
  | axiom (mentions : Array Name)
  /-- Anything else (a field over a type other than the class's sort parameters). -/
  | other
deriving Repr, BEq, Inhabited

namespace Signature

private def identName? (t : Term) : Option Name :=
  match t.raw with
  | .ident _ _ n _ => some n
  | _ => none

/-- All identifiers in a piece of syntax, in traversal order. -/
private partial def collectIdents : Syntax → Array Name
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.flatMap collectIdents
  | _ => #[]

/-- The natural-number literals in a piece of syntax (`3` in `x := x + 3`). -/
private partial def collectNumerals : Syntax → Array Int
  | .atom _ v => match v.toNat? with
    | some n => #[n]
    | none => #[]
  | .node _ _ args => args.flatMap collectNumerals
  | _ => #[]

/-- The symbol for a declared component, or an error for shapes UPDR does
not cover (non-sort argument or result types). A relation is a symbol over
its argument sorts; a `Bool` individual a 0-ary relation; a sort-valued
individual a 0-ary function; a `function` into a sort is a function symbol
and a `function` into `Bool` a relation (Veil writes `relation` that way). -/
private def componentSymbol (sorts : Array SortName) (sc : StateComponent)
    : MetaM (Option RelSym) := do
  let argSorts ← sc.domainTerms.mapM fun t => match identName? t with
    | some n =>
      if sorts.contains n then pure n
      else if isNumericSort n then throwError "IC3: {sc.kind} {sc.name} takes an integer argument; model the index as an ordered sort"
      else throwError "IC3: {sc.kind} {sc.name} has a non-sort argument type {t}"
    | none => throwError "IC3: {sc.kind} {sc.name} has a non-sort argument type {t}"
  match sc.kind with
  | .relation => return some { name := sc.name, source := .state, argSorts }
  | .individual =>
    match identName? sc.codomainTerm with
    | some `Bool => return some { name := sc.name, source := .boolIndividual, argSorts := #[] }
    | some s =>
      if sorts.contains s || isNumericSort s then
        return some { name := sc.name, source := .individualEq, argSorts := #[s] }
      else throwError "IC3: individual {sc.name} has unsupported type {sc.codomainTerm}"
    | none => throwError "IC3: individual {sc.name} has unsupported type {sc.codomainTerm}"
  | .function =>
    match identName? sc.codomainTerm with
    | some `Bool => return some { name := sc.name, source := .state, argSorts }
    | some s =>
      if sorts.contains s || isNumericSort s then
        return some { name := sc.name, source := .function, argSorts := argSorts.push s }
      else throwError "IC3: function {sc.name} has unsupported result type {sc.codomainTerm}"
    | none => throwError "IC3: function {sc.name} has unsupported result type {sc.codomainTerm}"
  | .module => throwError "IC3: child modules ({sc.name}) are not supported yet"

/-- Classify every field of class `className` instantiated at `sortArgs`
(the class's type parameters, in order, mapped to module sorts). A field whose
explicit arguments are all class parameters and whose result is `Prop` or
`Bool` is a relation over the corresponding sorts; a field with no arguments
whose type is a class parameter is a constant; a field with arguments, all
class parameters, whose result is a class parameter is a function; a field
whose type is a proposition is an axiom; a field whose result type is none
of these is `other`. A `Prop`-, `Bool`- or sort-valued field with an
argument outside the class parameters, or with an implicit argument, is an
error rather than `other`: such a field is a symbol over the module's sorts
that a universal clause could use, so leaving it out would weaken the
no-universal-invariant verdict.

Classes that extend another class, and constructor fields with a non-default
binder (`[dec : DecidableEq t]`), are rejected: Veil names inherited fields
through the parent projection (`inst.toParent.field`) and destructures such
constructors differently, so their symbols could not be matched to the
model's tables. -/
def classFieldSpecs (inst : Name) (className : Name) (sortArgs : Array SortName)
    : MetaM (Array (Name × FieldSpec)) := do
  let env ← getEnv
  let some indInfo := env.find? className
    | throwError "IC3: cannot resolve the class of instance {inst} ({className})"
  let numParams := match indInfo with
    | .inductInfo v => v.numParams
    | _ => 0
  if numParams != sortArgs.size then
    throwError "IC3: instance {inst} : {className} has {sortArgs.size} sort argument(s) but the class has {numParams} parameter(s)"
  let some structInfo := getStructureInfo? env className
    | throwError "IC3: {className} (instance {inst}) is not a structure-based class"
  for f in structInfo.fieldNames do
    if (isSubobjectField? env className f).isSome then
      throwError "IC3: class {className} (instance {inst}) extends another class; not supported yet"
  let ctor := getStructureCtor env className
  forallTelescopeReducing ctor.type fun xs _ => do
    for x in xs.extract numParams xs.size do
      let decl ← x.fvarId!.getDecl
      unless decl.binderInfo == .default do
        throwError "IC3: field {decl.userName} of class {className} (instance {inst}) has a non-default binder; not supported yet"
  let mut out := #[]
  for field in structInfo.fieldNames do
    let some projFn := getProjFnForField? env className field | continue
    let some info := env.find? projFn | continue
    let baseParams := numParams
    let spec ← forallTelescopeReducing info.type fun xs body => do
      -- The first `baseParams` binders are the class parameters, then `self`.
      if xs.size < baseParams + 1 then return FieldSpec.other
      let params := xs.extract 0 baseParams
      let sortOf (e : Expr) : Option SortName := do
        let i ← params.findIdx? (· == e)
        sortArgs[i]?
      let rest := xs.extract (baseParams + 1) xs.size
      let mut argSorts : Array SortName := #[]
      let mut ok := true
      let mut implicitArg := false
      for x in rest do
        let decl ← x.fvarId!.getDecl
        unless decl.binderInfo.isExplicit do implicitArg := true
        match sortOf decl.type with
        | some sName => argSorts := argSorts.push sName
        | none => ok := false
      if body.isProp || body == mkConst ``Bool then
        unless ok do
          throwError "IC3: field {field} of {className} (instance {inst}) is a relation over a non-sort type; not supported"
        if implicitArg then
          throwError "IC3: field {field} of {className} (instance {inst}) has an implicit argument; not supported"
        return FieldSpec.relation argSorts (body == mkConst ``Bool)
      if let some sName := sortOf body then
        if rest.isEmpty then return FieldSpec.const sName
        unless ok do
          throwError "IC3: field {field} of {className} (instance {inst}) is a function over a non-sort type; not supported"
        if implicitArg then
          throwError "IC3: field {field} of {className} (instance {inst}) has an implicit argument; not supported"
        return FieldSpec.function argSorts sName
      if ← Meta.isProp body then
        -- The statement of an axiom names the fields it constrains through
        -- their projection functions (`@TotalOrder.le t self x x`).
        let mentions := structInfo.fieldNames.filter fun f =>
          match getProjFnForField? env className f with
          | some pf => (info.type.find? (·.isConstOf pf)).isSome
          | none => false
        return FieldSpec.axiom mentions
      return FieldSpec.other
    out := out.push (field, spec)
  return out

/-- The symbols a typeclass instance `inst : C s₁ … sₙ` contributes: its
relation, constant and function fields. Axioms contribute nothing. A relation
or function field that cannot be represented is an error (see
`classFieldSpecs`): leaving a symbol out of the vocabulary would make the "no
universal invariant" verdict wrong. Fields outside the vocabulary are reported
under `trace.veil.synthesizer.debug` and returned as the third component
(`Signature.excludedClassFields`). The second component lists the keys of the
symbols no axiom of the class mentions (`Signature.freeClassSymbols`). -/
private def typeclassSymbols (inst : Name) (className : Name) (sortArgs : Array SortName)
    : MetaM (Array RelSym × Array Name × Array Name) := do
  let specs ← classFieldSpecs inst className sortArgs
  let constrained : Array Name := specs.flatMap fun (_, spec) => match spec with
    | .axiom mentions => mentions
    | _ => #[]
  let mut out : Array RelSym := #[]
  let mut free : Array Name := #[]
  let mut excluded : Array Name := #[]
  for (field, spec) in specs do
    let sym? : Option RelSym := match spec with
      | .relation argSorts _ => some { name := field, source := .typeclassField inst field, argSorts }
      | .const sName => some { name := field, source := .typeclassConst inst field, argSorts := #[sName] }
      | .function argSorts sName => some { name := field, source := .typeclassFn inst field, argSorts := argSorts.push sName }
      | .axiom _ | .other => none
    if spec matches .other then
      trace[veil.synthesizer.debug] "IC3: field {field} of {className} (instance {inst}) is outside the vocabulary: neither a relation, a sort constant nor a function between sorts"
      excluded := excluded.push (inst ++ field)
    if let some sym := sym? then
      out := out.push sym
      unless constrained.contains field do free := free.push sym.key
  return (out, free, excluded)

/-- The constructors of an enum sort, in declaration order, read from the
concrete inductive type Veil declares for it (`Mod.roleT_IndT`), each named as
a clause writes it. That is the bare name (`leader`), which Veil brings into
scope by opening the enum's class, unless the module declares the same name
(an action `leader`), which would capture it: then the name goes through the
class (`roleT_EnumClass.leader`). `Name.ctorBase` recovers the bare name. -/
def enumConstructors (mod : Veil.Module) (sort : SortName) : MetaM (Array Name) := do
  let typeName := mod.name ++ Name.toEnumConcreteTypeName sort
  let env ← getEnv
  match env.find? typeName with
  | some (.inductInfo info) =>
    let clauseName (ctor : Name) : Name :=
      if env.contains (mod.name ++ ctor) then Name.toEnumClass sort ++ ctor else ctor
    return info.ctors.toArray.map fun c => clauseName (c.updatePrefix .anonymous)
  | _ => throwError "IC3: cannot find the constructors of enum sort {sort} ({typeName})"

/-- The module's ghost definitions, by their names inside the module. Veil
keeps them as derived definitions of kind `ghost` (over theory and state) or
`theoryGhost` (over the theory alone). -/
def ghostDefinitions (mod : Veil.Module) : Array Name :=
  let names := mod._derivedDefinitions.toList.filterMap fun (n, dd) =>
    match dd.kind with
    | .ghost _ | .theoryGhost _ => some (n.replacePrefix mod.name .anonymous)
    | _ => none
  names.toArray.qsort fun a b => a.toString < b.toString

/-- Build the signature from the module's declared components, enum sorts and
instantiated typeclasses, and record its ghost definitions. Child modules,
module parameters and classes outside `classFieldSpecs`' shape are rejected
with a message. -/
def ofModule (mod : Veil.Module) : MetaM Signature := do
  let sorts := mod.sortParams.map (·.1.name)
  let mut enums : Array (SortName × Array Name) := #[]
  for (p, kind) in mod.sortParams do
    if kind == .enumSort then enums := enums.push (p.name, ← enumConstructors mod p.name)
  -- The instance Veil declares for an enum's class (`roleT_Enum`): its
  -- constants are the constructors, already in the vocabulary.
  let enumInsts := enums.map fun (s, _) => Name.toEnumInst s
  let mut stateRels : Array RelSym := #[]
  let mut immutableComponents : Array RelSym := #[]
  for sc in mod.signature do
    match sc.mutability with
    | .mutable => if let some sym ← componentSymbol sorts sc then stateRels := stateRels.push sym
    | .immutable => if let some sym ← componentSymbol sorts sc then immutableComponents := immutableComponents.push sym
    | .inherit => throwError "IC3: child modules ({sc.name}) are not supported yet"
  let mut classSymbols : Array RelSym := #[]
  let mut freeClassSymbols : Array Name := #[]
  let mut excludedClassFields : Array Name := #[]
  let mut typeclassInsts : Array (Name × Name × Array SortName) := #[]
  for p in mod.parameters do
    match p.kind with
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined =>
      if enumInsts.contains p.name then continue
      -- `TotalOrder node`, `ByzNodeSet node nset`, `Cfg`: the first identifier
      -- names the class, the following module-sort identifiers are its
      -- arguments, matched to the class parameters by position. A class with no
      -- sort parameter still contributes its 0-ary predicates.
      let idents := collectIdents p.type.raw
      let some classIdent := idents[0]?
        | throwError "IC3: cannot read the class of instance {p.name}"
      let className ← try resolveGlobalConstNoOverload (mkIdent classIdent)
        catch _ => throwError "IC3: cannot resolve the class of instance {p.name} ({classIdent})"
      -- Sort assumptions carry no vocabulary.
      if [``Inhabited, ``Nonempty, ``DecidableEq].contains className then continue
      unless isStructure (← getEnv) className do
        throwError "IC3: {className} (instance {p.name}) is not a structure-based class; not supported"
      let sortArgs := (idents.extract 1 idents.size).filter sorts.contains
      let (syms, free, excluded) ← typeclassSymbols p.name className sortArgs
      classSymbols := classSymbols ++ syms
      freeClassSymbols := freeClassSymbols ++ free
      excludedClassFields := excludedClassFields ++ excluded
      typeclassInsts := typeclassInsts.push (p.name, className, sortArgs)
    | .userParameter => throwError "IC3: module parameter {p.name} is not supported yet"
    -- Veil's own parameters carry no vocabulary. The sorts were read from
    -- `mod.sortParams` above; the mode parameter of `.do` definitions, the
    -- concrete field type `χ`, the environment state and background theory
    -- of a module embedded in another, per-definition parameters and the
    -- theory and state arguments of state predicates are plumbing.
    | .mode | .sort _ | .fieldConcreteType | .environmentState | .backgroundTheory
    | .definitionParameter .. | .theoryArg | .stateArg => pure ()
    -- Typeclass assumptions Veil makes for itself: the sub-state and
    -- sub-theory embeddings into an enclosing environment and the
    -- field-representation classes of the state's concrete type. None
    -- declares a symbol over the module's sorts.
    | .moduleTypeclass .backgroundTheory | .moduleTypeclass .environmentState
    | .moduleTypeclass .fieldRepresentation | .moduleTypeclass .lawfulFieldRepresentation => pure ()
  -- Clause variables are named `x0, x1, …`; a module identifier of that shape
  -- would be captured inside rendered clauses.
  let isVarName (n : Name) : Bool :=
    let str := n.toString
    str.startsWith "x" && str.length > 1 && (str.drop 1).all Char.isDigit
  let ctorNames := enums.flatMap (·.2)
  for n in sorts ++ (stateRels ++ immutableComponents).map (·.name) ++ mod.parameters.map (·.name) ++ ctorNames do
    if isVarName n then throwError "IC3: the name {n} clashes with clause variable names (x0, x1, …); rename it"
  let numericSorts := (stateRels ++ immutableComponents).foldl (init := #[]) fun acc sym =>
    match sym.argSorts.back? with
    | some s => if sym.isNumeric && !acc.contains s then acc.push s else acc
    | none => acc
  let numerals := if numericSorts.isEmpty then #[] else
    let raw := (mod.procedures.flatMap fun p => collectNumerals p.code.raw)
      ++ (mod.assertions.flatMap fun a => collectNumerals a.term.raw)
    let dedup : Array Int := (#[0, 1] ++ raw).foldl (fun (acc : Array Int) (n : Int) => if acc.contains n then acc else acc.push n) #[]
    dedup.qsort (· < ·)
  return { sorts, enums, stateRels, immutableComponents, classSymbols, typeclassInsts, freeClassSymbols,
           ghosts := ghostDefinitions mod, excludedClassFields, numericSorts, numerals }

/-- Whether the vocabulary has a symbol outside the shapes Proposition 5.6 of
the paper is stated for: a function symbol with arguments (a module
`function`, or a class field that is a function between sorts) or an enum
sort. The paper covers constants and relations, and a sort-valued individual
or class constant is a constant of its vocabulary. For the shapes named here
the no-universal-invariant verdict rests on this tool's extension of the
paper's argument (`analyzeCEX` in `Controller.lean`), which the verdict
message says. -/
def extendsPaper (sig : Signature) : Bool :=
  !sig.enums.isEmpty ||
    (sig.stateRels ++ sig.immutableComponents ++ sig.classSymbols).any fun sym =>
      sym.isFunction && sym.argSorts.size > 1

/-- The heads of the assignments in a `do` block: for `f a b := e` and
`f a b := *`, the identifier `f`. Nested blocks (`if`) are scanned too. -/
private partial def assignmentHeads : Syntax → Array Name
  | stx@(.node _ kind args) =>
    if kind == ``Lean.Parser.Term.doReassign || kind == ``Veil.havocAssignment then
      match (collectIdents stx)[0]? with
      | some n => #[n]
      | none => #[]
    else args.flatMap assignmentHeads
  | _ => #[]

/-- Mutable components that `after_init` never assigns. Such a component keeps
its `default` value in every initial state of Veil's transition system, while
`#check_invariants` proves initiation from an arbitrary pre-state, so a clause
certified here can fail that check (see `Certificate.lean`). The scan is
syntactic: an assignment made inside a procedure that `after_init` calls is
not seen. -/
def unassignedByInit (mod : Veil.Module) : Array Name :=
  match mod.procedures.find? (·.info matches .initializer) with
  | none => #[]
  | some p =>
    let heads := assignmentHeads p.code.raw
    (mod.signature.filter fun sc => sc.mutability matches .mutable && !heads.contains sc.name).map (·.name)

end Signature

/-! ## JSON decoding -/

private def parseFin? (s : String) : Option Nat :=
  if s.startsWith "Fin " then (s.drop 4).trimAscii.toNat? else none

private def natOfJson? : Json → Option Nat
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then some n.mantissa.toNat else none
  | _ => none

private def intOfJson? : Json → Option Int
  | .num n => if n.exponent == 0 then some n.mantissa else none
  | _ => none

/-- Leaves of a (possibly nested) JSON array, in order. Veil encodes a
`k`-tuple as left-nested pairs, so `((a,b),c)` arrives as `[[a,b],c]`, and a
function row as a flat `[a₁, …, aₙ, value]`. -/
private partial def leaves : Json → Array Json
  | .arr xs => xs.flatMap leaves
  | j => #[j]

/-- The sorts and enums of the structure being decoded, for reading elements. -/
private structure Carrier where
  sorts : Array (SortName × Nat)
  enums : Array (SortName × Array Name)

/-- An element of sort `s` from its JSON form: an index for an uninterpreted
sort, a constructor name for an enum sort. -/
private def elementOfJson (c : Carrier) (s : SortName) (j : Json) : Except String Nat :=
  match c.enums.find? (·.1 == s) with
  | some (_, ctors) =>
    match j with
    | .str name =>
      match ctors.findIdx? (·.ctorBase == name) with
      | some i => pure i
      | none => throw s!"{name} is not a constructor of enum sort {s}"
    | _ => throw s!"element {j} of enum sort {s} is not a constructor name; the model did not resolve the enum sort to its concrete type"
  | none => match natOfJson? j with
    | some v =>
      let size := ((c.sorts.find? (·.1 == s)).map (·.2)).getD 0
      if v < size then pure v
      else throw s!"element {v} of sort {s} is out of range; the sort has {size} element(s)"
    | none => throw s!"element {j} of sort {s} is not an index"

/-- A symbol's table from its JSON form. A relation of arity `k` is a list of
rows, each row a nested tuple with `k` leaves (a unary relation's rows are
bare elements); a `Bool` individual is a boolean (`true` = the empty tuple
holds); a function is a list of rows `args ++ [value]`; a sort-valued
individual is a bare value. A function table must be total: one row per
argument tuple. -/
private def tableOfJson (c : Carrier) (sym : RelSym) : Json → Except String (Array (Array Nat)) := fun j => do
  let sorts := sym.argSorts
  let rows ← match j with
    | .bool b => if sorts.isEmpty then pure (if b then #[#[]] else #[]) else throw "boolean for a symbol of arity > 0"
    | .arr rows => rows.mapM fun row => do
        let ls := leaves row
        unless ls.size == sorts.size do throw s!"tuple of wrong shape {row} (expected arity {sorts.size})"
        (sorts.zip ls).mapM fun (s, l) => elementOfJson c s l
    | j => if sorts.size == 1 then pure #[#[← elementOfJson c sorts[0]! j]] else throw s!"scalar {j} for a symbol of arity ≠ 1"
  if sym.isFunction then
    let m : FinStructure := { sorts := c.sorts, enums := c.enums, rels := #[] }
    let domain := m.tuples sorts.pop
    unless rows.size == domain.size && domain.all (fun t => rows.any (·.pop == t)) do
      throw s!"function table has {rows.size} row(s) for {domain.size} argument tuple(s); it must be total"
  return rows

/-- The value table of a numeric-valued symbol: a bare integer for an
`individual`, a list of rows `args ++ [value]` for a `function`, one row per
argument tuple. -/
private def numTableOfJson (c : Carrier) (sym : RelSym) : Json → Except String (Array (Array Nat × Int)) := fun j => do
  let argSorts := sym.argSorts.pop
  if argSorts.isEmpty then
    match intOfJson? j with
    | some v => return #[(#[], v)]
    | none => throw s!"value {j} is not an integer"
  match j with
  | .arr rows =>
    let rows ← rows.mapM fun row => do
      let ls := leaves row
      unless ls.size == argSorts.size + 1 do throw s!"row of wrong shape {row} (expected {argSorts.size} argument(s) and a value)"
      let args ← (argSorts.zip ls.pop).mapM fun (s, l) => elementOfJson c s l
      let some v := intOfJson? ls.back! | throw s!"value {ls.back!} is not an integer"
      pure (args, v)
    let m : FinStructure := { sorts := c.sorts, enums := c.enums, rels := #[] }
    let domain := m.tuples argSorts
    unless rows.size == domain.size && domain.all (fun t => rows.any (·.1 == t)) do
      throw s!"function table has {rows.size} row(s) for {domain.size} argument tuple(s); it must be total"
    return rows
  | _ => throw s!"{j} is not a function table"

/-- The table of a typeclass symbol that the model does not mention. lean-smt
reports every uninterpreted symbol that occurs in the query, and the class
axioms are always among the hypotheses, so an absent symbol occurs in no axiom
and no conjunct: any interpretation completes the model. The empty relation,
or the function mapping every argument tuple to element `0`, is used, and
`decodeTrace` names the completed symbols in `DecodedTrace.completed`
(`SearchM.decode` reports them under `trace.veil.synthesizer.debug`). `structureOfState`
completes only the symbols in `Signature.freeClassSymbols`, those no axiom
mentions; a missing symbol that an axiom mentions is a decoding error. Should
a symbol still be completed wrongly, the blocking clause built from the
completed structure would exclude no state and the same structure would come
back from the next query, which `mainLoop` (frontier) and `discharge`
(predecessor) detect and report as an internal error. -/
private def defaultTable (c : Carrier) (sym : RelSym) : Array (Array Nat) :=
  if sym.isFunction then
    let m : FinStructure := { sorts := c.sorts, enums := c.enums, rels := #[] }
    (m.tuples sym.argSorts.pop).map (·.push 0)
  else #[]

/-- Decode one state into a structure over the signature: state components from
the state's `fields`, immutable components from the trace's `theory`, typeclass
symbols from `extraVals`. Also returns the typeclass symbols `extraVals` did
not mention, whose tables `defaultTable` supplied. -/
private def structureOfState (sig : Signature) (c : Carrier)
    (fields theoryJ extraVals : Json) : Except String (FinStructure × Array Name) := do
  let mut rels : Array (RelSym × Array (Array Nat)) := #[]
  let mut nums : Array (RelSym × Array (Array Nat × Int)) := #[]
  let mut completed : Array Name := #[]
  for sym in sig.stateRels do
    let v ← match fields.getObjVal? sym.name.toString with
      | .ok v => pure v
      | .error _ => throw s!"state has no field {sym.name}"
    if sym.isNumeric then
      nums := nums.push (sym, ← numTableOfJson c sym v |>.mapError (s!"field {sym.name}: " ++ ·))
    else
      rels := rels.push (sym, ← tableOfJson c sym v |>.mapError (s!"field {sym.name}: " ++ ·))
  for sym in sig.immutableComponents do
    let v ← match theoryJ.getObjVal? sym.name.toString with
      | .ok v => pure v
      | .error _ => throw s!"model theory has no field {sym.name}"
    if sym.isNumeric then
      nums := nums.push (sym, ← numTableOfJson c sym v |>.mapError (s!"theory field {sym.name}: " ++ ·))
    else
      rels := rels.push (sym, ← tableOfJson c sym v |>.mapError (s!"theory field {sym.name}: " ++ ·))
  for sym in sig.classSymbols do
    let key := sym.key.toString
    let table ← match extraVals.getObjVal? key with
      | .ok v => tableOfJson c sym v |>.mapError (s!"symbol {key}: " ++ ·)
      | .error _ =>
        -- A key such as `b.toRBase.r` means the model names the field through
        -- a projection the vocabulary keyed differently: not a missing symbol.
        -- Only a key of the same instance is such a projection: `l.p` says
        -- nothing about `r.p`.
        let inst : Name := match sym.source with
          | .typeclassField i _ | .typeclassConst i _ | .typeclassFn i _ => i
          | _ => .anonymous
        let pre := inst.toString ++ "."
        let suffix := "." ++ sym.name.toString
        let clash : Option String := match extraVals with
          | .obj kvs => (kvs.toArray.find? fun (k, _) => k.startsWith pre && k.endsWith suffix).map (·.1)
          | _ => none
        if let some k := clash then throw s!"model names {k} where the vocabulary expected {key}"
        unless sig.freeClassSymbols.contains sym.key do
          throw s!"the model does not mention {key}, which an axiom of its class constrains; every such symbol is declared in the query and reported by the solver"
        completed := completed.push sym.key
        pure (defaultTable c sym)
    rels := rels.push (sym, table)
  return ({ sorts := c.sorts, enums := c.enums, rels, nums }, completed)

/-- A decoded trace: the structures of its states and the JSON of each
transition label (`{"recv": {...}}`), which we keep opaque. -/
structure DecodedTrace where
  sorts : Array (SortName × Nat)
  states : Array FinStructure
  labels : Array Json
  /-- Typeclass symbols the model did not mention, completed by `defaultTable`. -/
  completed : Array Name := #[]
deriving Inhabited

/-- Decode `VeilTrace.toJson` output. An uninterpreted sort's size is read
from its `Fin n` instantiation; an enum sort's size is its number of
constructors. -/
def decodeTrace (sig : Signature) (j : Json) : Except String DecodedTrace := do
  let inst ← j.getObjVal? "instantiation" |>.mapError toString
  let extraVals := (j.getObjVal? "extraVals").toOption.getD (.obj {})
  let theoryJ := (j.getObjVal? "theory").toOption.getD (.obj {})
  let sorts ← sig.sorts.mapM fun s => do
    if let some (_, ctors) := sig.enums.find? (·.1 == s) then return (s, ctors.size)
    match inst.getObjVal? s.toString with
    | .ok (.str t) => match parseFin? t with
      | some n => pure (s, n)
      | none => throw s!"sort {s} instantiated at non-Fin type {t}"
    | _ => throw s!"instantiation lacks sort {s}"
  let c : Carrier := { sorts, enums := sig.enums }
  let statesJ ← j.getObjVal? "states" |>.mapError toString
  let statesArr ← match statesJ with | .arr a => pure a | _ => throw "states is not an array"
  let mut states := #[]
  let mut labels := #[]
  let mut completed : Array Name := #[]
  for st in statesArr do
    let fields ← st.getObjVal? "fields" |>.mapError toString
    let (σ, cs) ← structureOfState sig c fields theoryJ extraVals
    states := states.push σ
    for n in cs do unless completed.contains n do completed := completed.push n
    labels := labels.push ((st.getObjVal? "transition").toOption.getD .null)
  return { sorts, states, labels, completed }

end Veil.Synthesizer
