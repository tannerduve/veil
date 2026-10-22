module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Query
public meta import Veil.Core.Tools.Synthesizer.Controller
public import Veil.Core.Tools.Synthesizer.Soundness

/-!
# The safety certificate

At a fixpoint the controller has clauses `c₁ … cₖ` such that, with the
property `P = p₁ ∧ … ∧ pₘ`, the conjunction `Inv = p₁ ∧ … ∧ pₘ ∧ c₁ ∧ … ∧ cₖ`
is inductive. This file turns that into a theorem in the module's namespace:

    theorem Mod.ic3_safe : ∀ sorts [instances] th st,
      (Mod.relationalTransitionSystem sorts).reachable th st → Mod.ic3_prop sorts th st

The transition system is Veil's `relationalTransitionSystem`: its initial
states are the results of running `after_init` from the default state (a
field `after_init` never assigns keeps its default value), its transitions are
the module's actions, and its `assumptions` are the module's `assumption`s.
`trusted invariant`s are not part of it and are not assumed. Veil's
`#check_invariants` proves initiation from an arbitrary pre-state instead, so
a clause certified here can still fail that check when `after_init` leaves a
field unassigned.

The proof is assembled, not searched for:

1. For every conjunct `q` of `Inv`, two solver queries are re-run against
   the final frame and their proof terms are added to the environment as
   theorems `Mod.ic3_init_i : ∀ …, ¬ (assumptions ∧ init st0 ∧ ¬ q st0)` and
   `Mod.ic3_cons_i : ∀ …, ¬ (assumptions ∧ Inv-conjuncts st0 ∧ step st0 st1 ∧ ¬ q st1)`,
   where `step` is the tagged disjunction over actions from `Query.lean`,
   written with the normalized transition relation `Mod.ic3_trNorm`
   (`QueryCtx.ensureTrNorm`) in place of `tr`. A consecution theorem whose
   proof could be replayed only from the plain form of its statement, with
   `tr`, is named `Mod.ic3_cons_i_tr`; a step taken on the solver's word is
   named `Mod.ic3_init_i_trusted` or `Mod.ic3_cons_i_trusted`
   (`proveObligation`).
2. `Mod.ic3_inv` and `Mod.ic3_prop` are defined as conjunctions of the
   wrapped predicates.
3. `Mod.ic3_safe` is proved by `Veil.Synthesizer.property_of_certificate`. Initiation
   and consecution come from the theorems of step 1 by
   `Classical.byContradiction`; consecution matches on the label and, per
   action, instantiates the query's universally quantified `ActionTag` with
   the module's concrete tag type and, for a theorem stated with
   `ic3_trNorm`, turns the hypothesis `tr th s (Label.a args) s'` into
   `ic3_trNorm …` by `Eq.mp` along the kernel-checked `Mod.ic3_tr_eq_norm`.

Every declaration is checked by the kernel before the command finishes. The
theorems of step 1, whose proofs come from the solver, go through
`addCheckedDecl`: the kernel checks each in a dry run and a rejected one is
never added, so a solver's claim cannot stay in the module as an axiom under
a theorem's name. `ic3_inv`, `ic3_prop` and `ic3_safe` are ordinary
declarations elaborated synchronously (`elabChecked`): the kernel checks them
before the command finishes and a rejection is an error of the command, after
which Lean keeps an axiom of the rejected name, as it does for any
declaration it rejects. Their terms are the elaborator's, assembled from the
checked theorems, so that rejection would be a bug of the assembly, not a
claim of the solver. With proof reconstruction (always on for certificates),
`#print axioms Mod.ic3_safe` lists the three standard axioms only: `propext`,
`Classical.choice` and `Quot.sound`. The exception is a solver step lean-smt
cannot reconstruct or the kernel rejects in both forms of its statement; it
is taken on the solver's word under a `_trusted` name (`addTrustedTheorem`),
a warning names it, the theorem then depends on `sorryAx` as well, and the
command reports that.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil Lean.Parser.Term

/-- The axioms a fully checked development rests on. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- What `certify` or `certifyUnsafe` put in the environment. -/
structure CertificateResult where
  /-- The theorem: `ic3_safe` or `ic3_unsafe`. -/
  theoremName : Name
  /-- The predicate the theorem is about: `ic3_inv` for a safety certificate,
  `ic3_prop` for a refutation. -/
  strengtheningName : Name
  /-- Axioms the final theorem depends on. -/
  axioms : Array Name
  /-- Every axiom is one of `standardAxioms`. -/
  kernelChecked : Bool
  /-- The axioms outside `standardAxioms` (`sorryAx` when a solver step was trusted). -/
  offenders : Array Name

/-- The result record for a theorem that is now in the environment. -/
def certificateResult (theoremName strengtheningName : Name) : CoreM CertificateResult := do
  let axioms ← Lean.collectAxioms theoremName
  let offenders := axioms.filter (!standardAxioms.contains ·)
  return { theoremName, strengtheningName, axioms, kernelChecked := offenders.isEmpty, offenders }

/-- Fail when a certificate declaration is already in the environment: a
module holds one certificate, since the theorem names are fixed. -/
def throwIfCertified (mod : Veil.Module) (names : List Name) : CommandElabM Unit := do
  for n in names do
    let full := mod.name ++ n
    if (← getEnv).contains full then
      throwError "IC3 certificate: {full} is already declared; a module can hold one certificate, so run `#synthesize_invariants … certify` once per module"

/-- `liftTermElabM` without the command's heartbeat limit: the certificate's
queries and declarations are not subject to `maxHeartbeats`. -/
def liftUnbounded (x : TermElabM α) : CommandElabM α :=
  liftTermElabM <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 0 }) x

/-- Run a certificate query without a model. An answer the solver itself gave
up on (`QueryResult.solverGaveUp`: a timeout or an `unknown` verdict) is asked
once more with twice the solver timeout: a certificate query restates a fact
the search established, in the one-hypothesis-per-conjunct shape the proof
assembly needs, and a fact at the edge of the solver's budget can fall on
either side of it. The other `unknown` reasons (a preprocessing failure, the
per-query heartbeat budget) would repeat and are not asked again. -/
def runCertificateQuery (mod : Veil.Module) (stmt : Term) (numTransitions : Nat) : TermElabM QueryResult := do
  match ← runStatement mod stmt numTransitions (wantModel := false) with
  | r@(.unknown reason) =>
    unless r.solverGaveUp do return r
    let t := veil.smt.timeout.get (← getOptions)
    logInfo s!"IC3 certificate: a query returned unknown ({reason.take 160}); asking again with veil.smt.timeout {2 * t}"
    withOptions (fun o => veil.smt.timeout.set o (2 * t)) do
      runStatement mod stmt numTransitions (wantModel := false)
  | r => pure r

private def mkThmName (mod : Veil.Module) (base : String) (i : Nat) : Name :=
  mod.name ++ Name.mkSimple s!"ic3_{base}_{i}"

/-- Add a closed proof term of a closed statement as a theorem, through
`addCheckedDecl`: the kernel checks it now, a rejection is an error of this
command, and a rejected proof leaves nothing in the environment, so `name`
stays free for another attempt. -/
private def addProofTheorem (name : Name) (ty pf : Expr) : MetaM Unit := do
  let ty ← instantiateMVars ty
  let pf ← instantiateMVars pf
  QueryCtx.addCheckedDecl <| Declaration.thmDecl ⟨⟨name, [], ty⟩, pf, [name]⟩

/-- The statement admitted outright: `sorryAx ty false`, a proof term of `ty`
that the kernel accepts whatever `ty` is, for the trusted theorem when
lean-smt's partial reconstruction is itself ill-typed. -/
def admittedProof (ty : Expr) : Expr :=
  mkApp2 (mkConst ``sorryAx [Level.zero]) ty (mkConst ``Bool.false)

/-- Add `pf`, a proof taken on the solver's word, as the theorem `name : ty`.
`pf` is lean-smt's partial reconstruction of the solver's proof, with `sorry`
for the steps it could not replay, and can be ill-typed itself; when the
kernel rejects it the statement is admitted outright (`admittedProof`) under
the same name, and the kernel's message is returned so that the caller's
warning can say so. Either way the theorem exists and depends on `sorryAx`. -/
def addTrustedTheorem (name : Name) (ty pf : Expr) : CommandElabM (Option String) := do
  try
    liftUnbounded <| addProofTheorem name ty pf
    return none
  catch e =>
    liftUnbounded <| addProofTheorem name ty (admittedProof ty)
    return some ((← e.toMessageData.toString).take 160).toString

/-- `Or.inr (… (Or.inl h))` selecting disjunct `k` of `n` (right-nested `∨`). -/
private def wrapInr (h : Term) : Nat → TermElabM Term
  | 0 => pure h
  | i + 1 => do
    let inner ← wrapInr h i
    `(term| Or.inr $inner)

private def orInj (k n : Nat) (h : Term) : TermElabM Term := do
  if n ≤ 1 then return h
  let base ← if k == n - 1 then pure h else `(term| Or.inl $h)
  wrapInr base k

/-- `h.2.2.….1`: projection of conjunct `i` out of a right-nested conjunction of `n`. -/
private def proj (h : Term) (i n : Nat) : TermElabM Term := do
  let mut acc := h
  for _ in [:i] do acc ← `(term| ($acc).2)
  if i + 1 < n then acc ← `(term| ($acc).1)
  return acc

/-- `⟨t₀, t₁, …⟩`, or the single term. -/
private def tuple (ts : Array Term) : TermElabM Term := do
  match ts with
  | #[] => `(term| True.intro)
  | #[x] => pure x
  | _ => `(term| ⟨$ts,*⟩)

/-- An identifier no module name can capture: a fresh hygienic name. Sort
names are plain identifiers (`type s`), so a binder written as a plain `s`
would shadow the sort inside the generated proof. -/
private def freshIdent (n : Name) : CommandElabM Ident := do
  return mkIdent (← liftCoreM (mkFreshUserName n))

/-- Elaborate a generated command and fail if it logged an error. `elabCommand`
recovers from elaboration errors with `sorry`; a certificate that did not
elaborate must be reported as such, not as a solver trust. Proofs are
elaborated synchronously so that their errors are visible here, and without
a heartbeat limit. -/
def elabChecked (c : TSyntax `command) : CommandElabM Unit := do
  let countErrors : CommandElabM Nat := do
    pure ((← get).messages.toList.filter (·.severity == .error)).length
  let before ← countErrors
  elabCommand (← `(command| set_option $(mkIdent `Elab.async):ident false in
    set_option $(mkIdent `maxHeartbeats):ident 0 in $c))
  if (← countErrors) > before then
    throwError "IC3 certificate: a generated declaration failed to elaborate (see the errors above)"

/-- Define `name sorts [instances] : Theory → State → Prop` as the conjunction
of the given user-level predicates, each wrapped by `QueryCtx.wrapPred`. This
is how `ic3_inv` and `ic3_prop` are declared, inside the module's namespace. -/
def definePredicate (ctx : QueryCtx) (name : Ident) (conjuncts : Array Term) : CommandElabM Unit := do
  let wrapped ← liftTermElabM (conjuncts.mapM ctx.wrapPred)
  let binders := ctx.sortBinders ++ ctx.typeclassBinders
  let th := mkIdent `th
  let st := mkIdent `st
  let body ← liftTermElabM <| repeatedAnd (← wrapped.mapM fun w => `(term| $w $th $st))
  elabChecked (← `(command| def $name $binders* : $(ctx.theoryT) → $(ctx.stateT) → Prop :=
    fun $th $st => $body))

/-- Prove one obligation of the certificate and add it as a theorem; return
the theorem's name and whether its statement is the plain form, written with
Veil's `tr`.

The obligation is asked with proof reconstruction forced on (`veil.synthesizer.trust`
off, whatever the search ran with) and the replayed proof is added under
`name`, which the kernel checks. Two things can go wrong: lean-smt cannot
reconstruct a step (the answer then comes back trusted, a proof with `sorry`
in it), or the kernel rejects the replayed term (lean-smt turns some
integer-arithmetic steps into ill-typed terms), which leaves nothing in the
environment. A two-state obligation of a module with a normalized transition
relation has two forms, `stmt false` with `ic3_trNorm` and `stmt true` with
`tr`. They hand the solver the same assertions in another order, and a proof
that does not replay from one order can replay from the other, so the plain
form is tried next and its theorem is added under `name_tr`, the suffix
saying which form the theorem states. When no form replays, the obligation is
taken on the solver's word: a warning names it and says why, and the trusted
proof is added under `name_trusted`, so the theorem exists and depends on
`sorryAx`, which the command reports. That proof is lean-smt's partial
reconstruction, with `sorry` for the steps it could not replay, and it can be
ill-typed itself; when the kernel rejects it the statement is admitted
outright under the same name (`addTrustedTheorem`), and the warning says so.

Answers other than `unsat` end the certificate: a `sat` answer means the
obligation does not hold at the fixpoint; an `unknown` or `error` answer
means the solver gave no verdict or the query could not be posed, which is
not evidence about the obligation. The exception is a second form that gets
no verdict while the first form's trusted proof is in hand: the obligation is
then taken on the solver's word as above. -/
private def proveObligation (mod : Veil.Module) (name : Name) (stmt : (plainTr : Bool) → TermElabM Term)
    (twoForms : Bool) (k : Nat) (what : String) : CommandElabM (Name × Bool) := do
  let ask (plainTr trusting : Bool) : TermElabM QueryResult :=
    withOptions (fun o => veil.synthesizer.trust.set o trusting) do
      runCertificateQuery mod (← stmt plainTr) k
  let formNote (plainTr : Bool) : String :=
    if !twoForms then "" else if plainTr then " in the plain form of the statement" else " in the normalized form of the statement"
  -- The message for an answer that is not `unsat`.
  let noProof (plainTr : Bool) (r : QueryResult) : String := match r with
    | .sat _ | .satUndecoded _ => s!"IC3 certificate: {what} did not hold at the fixpoint{formNote plainTr}"
    | .unknown reason => s!"IC3 certificate: the solver could not decide {what}{formNote plainTr} ({reason})"
    | .error e => s!"IC3 certificate: the query for {what}{formNote plainTr} could not be posed or its answer read ({e})"
    | .unsat .. => ""
  let forms : Array (Bool × Name) :=
    if twoForms then #[(false, name), (true, name.appendAfter "_tr")] else #[(false, name)]
  let mut failures : Array String := #[]
  -- A trusted proof that came back from a form whose replay failed, reused
  -- for the `_trusted` theorem instead of asking once more.
  let mut onFaith : Option (Expr × Expr × Bool) := none
  for (plainTr, thmName) in forms do
    let r ← liftUnbounded (ask plainTr false)
    let .unsat ty pf viaTrust := r
      | match r with
        | .sat _ | .satUndecoded _ => throwError "{noProof plainTr r}"
        | _ =>
          -- No verdict for this form. With a trusted proof of the other form
          -- in hand the obligation is still taken on the solver's word;
          -- without one nothing supports it.
          unless onFaith.isSome do throwError "{noProof plainTr r}"
          failures := failures.push s!"no verdict{formNote plainTr} ({r})"
          continue
    if viaTrust then
      failures := failures.push s!"lean-smt could not reconstruct the solver's proof{formNote plainTr}"
      onFaith := some (ty, pf, plainTr)
      continue
    try
      liftUnbounded <| addProofTheorem thmName ty pf
      if plainTr then
        logInfo m!"IC3 certificate: {what} was replayed{formNote plainTr} after the first attempt failed ({"; ".intercalate failures.toList})"
      return (thmName, plainTr)
    catch e =>
      failures := failures.push s!"the kernel rejected the replayed proof{formNote plainTr} ({((← e.toMessageData.toString).take 160).toString})"
  let (ty, pf, plainTr) ← match onFaith with
    | some t => pure t
    | none => do
      -- Both forms were rejected by the kernel: ask once more trusting the
      -- solver, whose answer is a plain admitted proof.
      match ← liftUnbounded (ask false true) with
      | .unsat ty pf _ => pure (ty, pf, false)
      | r => throwError "{noProof false r}"
  let name' := name.appendAfter "_trusted"
  if let some rejection ← addTrustedTheorem name' ty pf then
    failures := failures.push s!"the kernel rejected the partially reconstructed proof as well ({rejection}), so the statement is admitted outright"
  logWarning m!"IC3 certificate: {what} is taken on the solver's word: {"; ".intercalate failures.toList}"
  return (name', plainTr)

/-- Build and check the certificate for the clauses of a fixpoint frame. -/
def certify (mod : Veil.Module) (property : Array Term) (clauses : Array Clause)
    : CommandElabM CertificateResult := do
  throwIfCertified mod [`ic3_init_0, `ic3_prop, `ic3_safe]
  let ctx ← liftTermElabM (QueryCtx.ofModule mod)
  let conj : Array Term := property ++ (← liftTermElabM (clauses.mapM (·.toTerm)))
  let n := conj.size
  let sortIdents := ctx.sorts
  -- 1. Per-conjunct theorems from fresh solver runs against the final frame.
  -- The consecution statements are written by `stepDisjunction` with the
  -- normalized transition relation when the module has one; `consPlain[i]`
  -- says that conjunct `i`'s theorem is in the plain form instead.
  let trNorm? ← liftUnbounded ctx.ensureTrNorm
  let mut initNames : Array Name := #[]
  let mut consNames : Array Name := #[]
  let mut consPlain : Array Bool := #[]
  for i in [:n] do
    let q := conj[i]!
    let (initName, _) ← proveObligation mod (mkThmName mod "init" i) (fun _ => ctx.oneState true #[] q) false 0
      s!"initiation of conjunct {i}"
    initNames := initNames.push initName
    let (consName, plainTr) ← proveObligation mod (mkThmName mod "cons" i)
      (fun plainTr => ctx.twoState conj q (separate := true) (plainTr := plainTr)) trNorm?.isSome 1
      s!"consecution of conjunct {i}"
    consNames := consNames.push consName
    consPlain := consPlain.push plainTr
  -- 2. `ic3_inv` and `ic3_prop`, declared inside the module's namespace.
  let strengthName := mkIdent `ic3_inv
  let propName := mkIdent `ic3_prop
  definePredicate ctx strengthName conj
  definePredicate ctx propName property
  let binders := ctx.sortBinders ++ ctx.typeclassBinders
  let th := mkIdent `th
  let st := mkIdent `st
  -- 3. The final theorem. Its binders are fresh names so that a module sort
  -- or component of the same spelling cannot capture them.
  let has ← freshIdent `has
  let s0 ← freshIdent `s
  let s1 ← freshIdent `s'
  let lbl ← freshIdent `lbl
  let htr ← freshIdent `htr
  let hinit ← freshIdent `hinit
  let hInv ← freshIdent `hInv
  let initProofs ← liftTermElabM <| (Array.range n).mapM fun i => do
    let thm := mkIdent initNames[i]!
    `(term| Classical.byContradiction fun hc => $thm $sortIdents* $th $s0 ⟨$has, $hinit, hc⟩)
  let initTuple ← liftTermElabM (tuple initProofs)
  let hConj ← liftTermElabM <| (Array.range n).mapM fun i => proj hInv i n
  let actionTagConcrete := Ident.toEnumConcreteType actionTagType
  let numActs := mod.actions.size
  -- The consecution statements quantify over the parameters of every action
  -- (in `mod.actions` order); the current action's constructor arguments fill
  -- its slots and every other slot takes `default` (sorts are `Inhabited`).
  let arities ← liftTermElabM <| mod.actions.mapM fun act => do
    let (_, specificParams) ← mod.declarationAllParams act.name act.declarationKind
    pure specificParams.size
  -- Consecution is a dependent `match` on the label (a term, not `cases` plus
  -- `case`: the `case` tactic renames the last hypotheses whose names carry
  -- macro scopes, which the fresh binders here do).
  let mut alts : Array (TSyntax ``matchAlt) := #[]
  for k in [:numActs] do
    let act := mod.actions[k]!
    let args ← (Array.range arities[k]!).mapM fun j => freshIdent (Name.mkSimple s!"a{j}")
    let allArgs : Array Term ← liftTermElabM do
      let mut out : Array Term := #[]
      for k' in [:numActs] do
        if k' == k then out := out ++ args.map (fun a => (a : Term))
        else for _ in [:arities[k']!] do out := out.push (← `(term| default))
      pure out
    let ctorName := mkIdent (labelTypeName ++ act.name)
    let tagMember := mkIdent (actionTagConcrete.getId ++ act.name)
    -- `htr : tr th s (Label.a args) s'`; a consecution theorem stated with
    -- the normalized relation, which `ic3_tr_eq_norm` equates to `tr`, takes
    -- the hypothesis rewritten along that equation.
    let trEq := mkIdent (QueryCtx.trEqNormName mod)
    let consProofs ← liftTermElabM <| (Array.range n).mapM fun i => do
      let thm := mkIdent consNames[i]!
      let htrStep ← if trNorm?.isSome && !consPlain[i]! then
          `(term| Eq.mp ($trEq $sortIdents* $th $s0 ($ctorName $args*) $s1) $htr)
        else pure (htr : Term)
      let disj ← orInj k numActs (← `(term| ⟨rfl, $htrStep⟩))
      `(term| Classical.byContradiction fun hc =>
          $thm $sortIdents* $actionTagConcrete inferInstance $tagMember $allArgs* $th $s0 $s1
            ⟨$has, $hConj,*, $disj, hc⟩)
    let consTuple ← liftTermElabM (tuple consProofs)
    let pat : Term ← liftTermElabM <| if args.isEmpty then pure ctorName else `(term| $ctorName $args*)
    alts := alts.push (← liftTermElabM `(matchAltExpr| | $pat, $htr => $consTuple))
  let consProof : Term ← liftTermElabM <|
    if numActs == 0 then `(term| nomatch $lbl) else `(term| match $lbl:ident, $htr:ident with $alts:matchAlt*)
  let propProj ← liftTermElabM do
    let ps ← (Array.range property.size).mapM fun i => proj hInv i n
    tuple ps
  let thmName := mkIdent `ic3_safe
  -- Applied to the sorts only; instance arguments are resolved from the binders.
  let rts ← liftTermElabM `(term| $assembledRTS $sortIdents*)
  elabChecked (← `(command|
    theorem $thmName $binders* : ∀ ($th : $(ctx.theoryT)) ($st : $(ctx.stateT)),
        ($rts).$(mkIdent `reachable) $th $st → $propName $sortIdents* $th $st :=
      Veil.Synthesizer.property_of_certificate ($rts) ($strengthName $sortIdents*) ($propName $sortIdents*)
        (fun $th $s0 $has $hinit => $initTuple)
        (fun $th $s0 $lbl $s1 $has $hInv $htr => $consProof)
        (fun $th $st $hInv => $propProj)))
  liftCoreM <| certificateResult (mod.name ++ thmName.getId) (mod.name ++ strengthName.getId)

end Veil.Synthesizer
