module

public meta import Veil
public meta import Veil.Core.Tools.ModelChecker.Symbolic.TraceLang
public meta import Veil.Core.UI.Verifier.TraceCounterexample
public meta import Veil.Frontend.DSL.Module.VCGen.Common
public meta import Veil.Core.Tools.Synthesizer.Clause
public meta import Veil.Core.Tools.Synthesizer.Render
public meta import Veil.Core.Tools.Synthesizer.Vocabulary

/-!
# Solver queries over a Veil module

Every question UPDR asks is a conjunction over the module's assembled
relational transition system `RTS`, in one of five shapes:

* `oneState`: `assumptions th ∧ [init th s] ∧ A₁ th s ∧ … ∧ Aₖ th s ∧ ¬ B th s`
  (initiation: `B` holds in every initial state; `B` is a clause or the
  property);
* `twoState`: `assumptions th ∧ [init th s] ∧ A₁ th s ∧ … ∧ tr th s l s' ∧ ¬ B th s'`
  (a predecessor of `¬B` in the frame `A₁ ∧ … ∧ Aₖ`; the controller's frontier
  query, which looks for a bad successor of the last frame, and its push
  queries, which move a clause up one frame, have this shape);
* `initLits` and `twoStateLits`: the same with `¬ B` replaced by the literals
  of a diagram under extra element binders (a *skolemized* diagram: its
  existential variables become universally bound variables of the statement,
  which is cheaper to preprocess and lets the unsat core, the set of
  hypotheses the solver used to derive the contradiction, name literals);
* `boundedPath`: `assumptions th ∧ init th s₀ ∧ tr th s₀ l₁ s₁ ∧ … ∧ ¬ B th sₖ`
  (a concrete counterexample of exactly `k` transitions).

We build the universally quantified negation of the conjunction as a `Term`,
exactly as Veil's `sat trace` does, and discharge it with Veil's `veil_bmc`
tactic pipeline. `unsat` means the conjunction is unsatisfiable and, when
proof reconstruction is on, comes with a Lean proof term of the statement;
`sat` comes with a decoded model.

The transition is written as a disjunction over actions tagged with an
`ActionTag` variable and per-action parameter variables named the way Veil's
trace decoder expects (`_tr1_act_recv_arg0_sender`), so a `sat` model decodes
through `buildTraceFromModel` without any code of our own.

The disjuncts do not mention Veil's `tr` but `Mod.ic3_trNorm th st0 (Label.a
args) st1`, the *normalized transition relation*: a definition this file adds
to the module once (`QueryCtx.ensureTrNorm`) whose body is, per action, the
proposition Veil's preprocessing makes of `tr th st0 (Label.a args) st1`,
together with the kernel-checked theorem `Mod.ic3_tr_eq_norm` that the two
are equal. The preprocessing of the transition relation is paid once per
module instead of once per query: `preprocessTactic` unfolds the definition
after its first two `simp` passes, and the solver sees the hypotheses it
would see with `tr`. The certificate states its consecution theorems with
`ic3_trNorm` and turns the transition hypothesis of the final theorem into
that form along the equation (`Certificate.lean`). The option
`veil.synthesizer.normalizeTr false` turns the normalization off; the queries are then
written with `tr`.

Veil's module representation is read here, in `Vocabulary.lean` (the vocabulary and
the model decoder), in `Controller.lean` and `Command.lean` (the safety,
invariant and trusted-invariant lists, `uqc%`) and in `Certificate.lean` /
`Counterexample.lean` (Veil's generated names for the transition system,
labels and action tags).
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil Lean.Parser.Term

/-- What a query returned. -/
inductive QueryResult where
  /-- The conjunction is unsatisfiable. `proof` is a proof of the universally
  quantified negation (the statement in `statement`); it contains `sorry` when
  the solver was trusted, under `veil.synthesizer.trust true` or on the re-ask that follows
  a proof lean-smt could not replay (`runStatementCore`). -/
  | unsat (statement : Expr) (proof : Expr) (viaTrust : Bool)
  /-- The conjunction is satisfiable; `model` is `VeilTrace.toJson` output
  (states `st0 … stₖ`), or `Json.null` when the query was asked without a model. -/
  | sat (model : Json)
  /-- The conjunction is satisfiable, but the model asked for could not be
  read (`reason`): lean-smt returned none, or Veil's decoder failed on it. A
  verdict all the same: a caller whose `sat` means a violation reports one. -/
  | satUndecoded (reason : String)
  /-- The solver gave up: timeout, `unknown`, heartbeat budget, or fuel. -/
  | unknown (reason : String)
  /-- The question could not be posed or its answer could not be read
  (elaboration failure, a proof-reconstruction exception). -/
  | error (message : String)

instance : ToString QueryResult := ⟨fun
  | .unsat _ _ viaTrust => s!"unsat{if viaTrust then " (solver trusted)" else ""}"
  | .sat _ => "sat"
  | .satUndecoded r => s!"sat, but the model could not be decoded: {r}"
  | .unknown r => s!"unknown: {r}"
  | .error m => s!"error: {m}"⟩

/-- The prefix of an `unknown` reason that came from the solver itself: a
timeout or an `unknown` verdict, as opposed to fuel, a preprocessing failure
or the per-query heartbeat budget. -/
def solverUnknownPrefix : String := "solver returned unknown"

/-- Whether the answer is an `unknown` the solver itself gave up on. Such an
answer may change with a larger `veil.smt.timeout`, which is why some callers
ask once more; the other `unknown` reasons would not. -/
def QueryResult.solverGaveUp : QueryResult → Bool
  | .unknown r => r.startsWith solverUnknownPrefix
  | _ => false

/-- Wall-clock milliseconds spent in each phase of the queries of this
process, summed over queries; `#synthesize_invariants` reports the difference
over one run. `normalizeMs` is the once-per-module normalization of the
transition relation (`QueryCtx.ensureTrNorm`), preprocessing moved out of
the queries, and is not part of any query's time. -/
structure QueryPhases where
  /-- Elaborating the statement to an `Expr`. -/
  elabMs : Nat := 0
  /-- Veil's preprocessing of the statement (`preprocessTactic`). -/
  preprocessMs : Nat := 0
  /-- The `smt` tactic: translation, the solver, proof reconstruction. -/
  smtMs : Nat := 0
  /-- Decoding a model into a trace. -/
  decodeMs : Nat := 0
  /-- `QueryCtx.ensureTrNorm`. -/
  normalizeMs : Nat := 0
deriving Repr, Inhabited

/-- Phase times of `a` minus those of `b`: the phases of a run are the
difference between the process totals at its end and at its start. -/
def QueryPhases.sub (a b : QueryPhases) : QueryPhases :=
  { elabMs := a.elabMs - b.elabMs, preprocessMs := a.preprocessMs - b.preprocessMs,
    smtMs := a.smtMs - b.smtMs, decodeMs := a.decodeMs - b.decodeMs, normalizeMs := a.normalizeMs - b.normalizeMs }

initialize queryPhases : IO.Ref QueryPhases ← IO.mkRef {}

/-- Add the milliseconds since `t0` to the phase `f` selects. -/
def notePhase (f : QueryPhases → Nat → QueryPhases) (t0 : Nat) : IO Unit := do
  let dt := (← IO.monoMsNow) - t0
  queryPhases.modify fun p => f p dt

/-- Whether the queries are written with the normalized transition relation
`Mod.ic3_trNorm` (`QueryCtx.ensureTrNorm`). Off, every query is written with
Veil's `tr` and pays its preprocessing, and the certificate states its
consecution theorems with `tr` as well. For exercising that path, and for
telling whether a change in a search came from the normalization. -/
register_option veil.synthesizer.normalizeTr : Bool := {
  defValue := true
  descr := "write the queries with the normalized transition relation `Mod.ic3_trNorm`, built once per module, instead of Veil's `tr`"
}

/-- Syntax pieces shared by every query against one module. -/
structure QueryCtx where
  mod : Veil.Module
  sorts : Array Ident
  sortBinders : Array (TSyntax ``bracketedBinder)
  typeclassBinders : Array (TSyntax ``bracketedBinder)
  th : Ident
  theoryT : Term
  stateT : Term
  rtsExpr : Term
  fieldRepInstance : Term
  stateSortTerm : Term

def QueryCtx.ofModule (mod : Veil.Module) : TermElabM QueryCtx := do
  let sorts ← mod.uninterpretedParamIdents
  let sortBinders ← mod.uninterpretedParamBinders
  let typeclassParams : Array Veil.Parameter := mod.parameters.filter fun p =>
    match p.kind with
    | .moduleTypeclass .sortAssumption | .moduleTypeclass .userDefined => true
    | _ => false
  let typeclassBinders ← typeclassParams.mapM (·.binder)
  let th := mkIdent `th
  let theoryT ← mod.theoryStx
  let stateT ← `(term| $(mkIdent stateName) ($fieldAbstractDispatcher $sorts*))
  let rtsExpr ← `(term| @$assembledRTS $sorts*)
  let fieldRepInstance ← `(term| $instAbstractFieldRepresentation $sorts*)
  let stateSortTerm ← `(term| $fieldAbstractDispatcher $sorts*)
  return { mod, sorts, sortBinders, typeclassBinders, th, theoryT, stateT, rtsExpr, fieldRepInstance, stateSortTerm }

namespace QueryCtx

/-- A user-level state predicate as a function `fun th st => …` over the
module's theory and state types, with its capitals universally quantified.
A *capital* is an identifier made only of uppercase letters and digits (`N`,
`N1`; not `Node`); Veil's `uqc%` binds every capital of a term with a
universal quantifier, which is how `safety holds C ∧ holds D → C = D` means
"for all `C`, `D`". The other builders below quantify capitals the same way. -/
def wrapPred (ctx : QueryCtx) (t : Term) : TermElabM Term := do
  withTheoryAndStateFn ctx.mod (← `(uqc% (($t:term):Prop))) (some (← `(term|Prop)))
    ctx.theoryT ctx.stateT ctx.fieldRepInstance ctx.stateSortTerm

/-- Apply a user-level state predicate (a `Term` over the module's relations,
capitals universally quantified) to a state variable. -/
def applyPred (ctx : QueryCtx) (t : Term) (st : Ident) : TermElabM Term := do
  let w ← ctx.wrapPred t
  `(term| ($w $(ctx.th) $st))

def stateIdent (i : Nat) : Ident := mkIdent (Name.mkSimple s!"st{i}")

/-! ### The normalized transition relation

`preprocessTactic` starts with two `simp` passes over the whole statement,
`simp only [nextSimp]` and the guarded existential simproc, and ends with
`simp only [smtSimp]`. On `tr th st0 (Label.a args) st1` they unfold the
action's semantics into a proposition over the fields of the two states, the
same in every query; the profile measured this as most of the preprocessing
time, flat in the frame size. `ensureTrNorm` does it once per module. -/

/-- `Mod.ic3_trNorm`: the normalized transition relation of the module. -/
def trNormName (mod : Veil.Module) : Name := mod.name ++ `ic3_trNorm

/-- `Mod.ic3_tr_eq_norm : ∀ …, tr th st0 lbl st1 = ic3_trNorm … th st0 lbl st1`. -/
def trEqNormName (mod : Veil.Module) : Name := mod.name ++ `ic3_tr_eq_norm

/-- The simp context and simprocs of a `simp only […]` tactic, as the tactic
itself elaborates them, so that a term-level `Meta.simp` applies the same
simp set as the tactic in `preprocessTactic`. -/
private def simpContextOf (tac : TSyntax `tactic) : TermElabM (Simp.Context × Simp.SimprocsArray) := do
  let g ← mkFreshExprMVar (mkConst ``True)
  let x : Tactic.TacticM (Simp.Context × Simp.SimprocsArray) := do
    let r ← Tactic.mkSimpContext tac (eraseLocal := false)
    pure (r.ctx, r.simprocs)
  x.run { elaborator := .anonymous } |>.run' { goals := [g.mvarId!] }

/-- Add a declaration the kernel accepts, and nothing when it does not. Lean's
`addDecl` registers a declaration the kernel rejects as an axiom of the same
name and type before it reports the rejection, which would leave a solver's
claim in the module as an unproven axiom under a theorem's name. So the
declaration is first checked in a dry run on the kernel's own view of the
environment (`Kernel.Environment.addDecl`, a pure function): a rejection is
thrown as this command's error and the environment is untouched. An accepted
declaration is then added without a second kernel pass
(`debug.skipKernelTC`), since the dry run checked it against the same
environment. Synchronous (`Elab.async false`) and without a heartbeat limit,
so the check finishes before the command reports anything. -/
def addCheckedDecl (d : Declaration) : CoreM Unit :=
  withOptions (fun o => maxHeartbeats.set (Elab.async.set o false) 0) do
    match Kernel.Environment.addDecl (← getEnv).toKernelEnv (← getOptions) d with
    | .error ex => throwKernelException ex
    | .ok _ => withOptions (fun o => debug.skipKernelTC.set o true) (addDecl d)

/-- What this process built for a module's normalized transition relation:
the type and value of `Mod.ic3_trNorm` and of `Mod.ic3_tr_eq_norm` as the
kernel checked them. -/
structure TrNormRecord where
  mod : Name
  defType : Expr
  defValue : Expr
  eqType : Expr
  eqValue : Expr

/-- Whether the environment holds the declarations of `built` under their
names: a definition `Mod.ic3_trNorm` and a theorem `Mod.ic3_tr_eq_norm` whose
types and values are the ones the kernel checked. The environment is a
snapshot per elaboration while the record lives as long as the process, so
the names alone say nothing: a later elaboration of the same file can hold a
declaration of another origin under them. -/
def TrNormRecord.holdsIn (built : TrNormRecord) (env : Environment) : Bool :=
  match env.find? (built.mod ++ `ic3_trNorm), env.find? (built.mod ++ `ic3_tr_eq_norm) with
  | some (.defnInfo d), some (.thmInfo t) =>
    d.type == built.defType && d.value == built.defValue && t.type == built.eqType && t.value == built.eqValue
  | _, _ => false

/-- Modules whose normalized transition relation this process built, with
the declarations it added and the kernel checked. Only those declarations
are written in queries (`trNormAvailable` compares the environment's
constants against the record); a declaration of the same name from anywhere
else, a module's own, one imported from an earlier build, or one that took
the place of the built pair in a later elaboration of the file, is a clash
(`throwIfTrNormForeign`), so the name alone is not taken as evidence that
the equation was proven. -/
initialize trNormBuilt : IO.Ref (Array TrNormRecord) ← IO.mkRef #[]

/-- The record of `mod`, when this process built its normalized transition relation. -/
def trNormRecord? (mod : Veil.Module) : IO (Option TrNormRecord) := do
  return (← trNormBuilt.get).find? (·.mod == mod.name)

/-- Modules whose normalization failed in this process. They are not tried
again; their queries are written with Veil's `tr`. -/
initialize trNormFailed : IO.Ref (Array Name) ← IO.mkRef #[]

/-- The normalized transition relation of `mod` when the queries are to use
it: `veil.synthesizer.normalizeTr` is on, this process built both its definition and its
equation, and the environment holds those two declarations under the names
(`TrNormRecord.holdsIn`). The name to write in queries and to unfold in
`preprocessTactic`. -/
def trNormAvailable (mod : Veil.Module) : CoreM (Option Name) := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return none
  let some built ← trNormRecord? mod | return none
  if built.holdsIn (← getEnv) then return some (trNormName mod) else return none

/-- Fail when `Mod.ic3_trNorm` or `Mod.ic3_tr_eq_norm` is in the environment
and is not the declaration this process built and the kernel checked
(`TrNormRecord.holdsIn`): the two names are reserved for the normalized
transition relation, and a declaration of another origin is not written in
queries in its place, whatever its type. A failed normalization leaves
neither name behind (`ensureTrNorm`). A run with `veil.synthesizer.normalizeTr` off does
not use the names and is exempt. -/
def throwIfTrNormForeign (mod : Veil.Module) : CoreM Unit := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return
  let env ← getEnv
  if let some built ← trNormRecord? mod then
    if built.holdsIn env then return
  for n in [trNormName mod, trEqNormName mod] do
    if env.contains n then
      throwError "IC3: {n} is already declared; the names `ic3_trNorm` and `ic3_tr_eq_norm` are reserved for the normalized transition relation the command builds"

/-- A fault hook for the regression tests: `ensureTrNorm` fails at the point
the value names, so the fallback to Veil's `tr` (its warning, its `failed`
status, the absence of a second attempt, the restored environment) can be
exercised. `"before"` fails before anything is built; `"afterDef"` fails
after `Mod.ic3_trNorm` has been added and before the equation is stated,
where a rejection of the equation would leave the definition behind if the
environment were not restored. The empty string, the default, is off; any
other value is an error (`failNormalizeAt`). No module is known whose
normalization fails on its own. -/
register_option veil.synthesizer.debug.failNormalize : String := {
  defValue := ""
  descr := "make the normalization of the transition relation fail \"before\" anything is built or \"afterDef\", after the definition and before the equation, to exercise the fallback to Veil's `tr` (for tests)"
}

/-- The fault point `veil.synthesizer.debug.failNormalize` names, or an error for a value
it does not define. `#synthesize_invariants` reads it before the run so that
a wrong value is an error of the command, not a failed query. -/
def failNormalizeAt : CoreM (Option String) := do
  match veil.synthesizer.debug.failNormalize.get (← getOptions) with
  | "" => return none
  | "before" => return some "before"
  | "afterDef" => return some "afterDef"
  | v => throwError "IC3: veil.synthesizer.debug.failNormalize is \"{v}\"; its values are \"before\" and \"afterDef\""

/-- Add `Mod.ic3_trNorm` and `Mod.ic3_tr_eq_norm` to the environment unless
it already holds the pair this process built (`trNormAvailable`), record
both declarations (`trNormBuilt`), and return the definition's name; `none`
when `veil.synthesizer.normalizeTr` is off or, with a warning the first time, when the
normalization fails, in which case the queries are written with Veil's `tr`
and pay its preprocessing on every call. A failure leaves the environment as
it was: the definition is added before the equation can be stated, so when
the equation is rejected the environment is restored to its state before the
attempt, and neither name is left behind (the fault hook
`veil.synthesizer.debug.failNormalize` exercises both failure points). The time of the
attempt, failed or not, is recorded in `QueryPhases.normalizeMs`.

The definition is `fun sorts [insts] th st0 lbl st1 => Label.casesOn lbl P₁ …
Pₙ` where `Pₐ args` is `tr th st0 (Label.a args) st1` after the three `simp`
passes of `preprocessTactic` (`nextSimp`, the guarded existential simproc,
`smtSimp`), run by `Meta.simp` with the tactic's own simp sets on the relation
under a telescope of its binders. The theorem is proven by cases on the
label; each case is the `simp` proof of that action's normalization, and the
kernel checks it against the definition by unfolding. Nothing about the
search rests on this: the theorem is a kernel-checked equation, and every use
is a rewrite along it. -/
def ensureTrNorm (ctx : QueryCtx) : TermElabM (Option Name) := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return none
  if let some name ← trNormAvailable ctx.mod then return some name
  if (← trNormFailed.get).contains ctx.mod.name then return none
  throwIfTrNormForeign ctx.mod
  let failAt ← failNormalizeAt
  let t0 ← IO.monoMsNow
  let envBefore ← getEnv
  let r ← tryCatchRuntimeEx
    (do
      if failAt == some "before" then
        throwError "injected failure, veil.synthesizer.debug.failNormalize before"
      let built ← buildTrNorm ctx failAt
      trNormBuilt.modify fun rs => (rs.filter (·.mod != ctx.mod.name)).push built
      pure (some (trNormName ctx.mod)))
    fun e => do
      setEnv envBefore
      trNormFailed.modify (·.push ctx.mod.name)
      logWarning m!"IC3: the transition relation of {ctx.mod.name} could not be normalized ({e.toMessageData}); its queries are written with Veil's `tr` and pay its preprocessing on every call"
      return none
  notePhase (fun p dt => { p with normalizeMs := p.normalizeMs + dt }) t0
  return r
where
  /-- Build and add the two declarations; `failAt` is the fault point of
  `veil.synthesizer.debug.failNormalize`. Returns what was added, for `trNormBuilt`. -/
  buildTrNorm (ctx : QueryCtx) (failAt : Option String) : TermElabM TrNormRecord := do
  let name := trNormName ctx.mod
  let eqName := trEqNormName ctx.mod
  let th := ctx.th
  let st0 := stateIdent 0
  let st1 := stateIdent 1
  let lbl := mkIdent `lbl
  let labelT ← `(term| $(mkIdent labelTypeName) $(ctx.sorts)*)
  let funBinders ← (ctx.sortBinders ++ ctx.typeclassBinders).mapM bracketedBinderToFunBinder
  let fnStx ← `(term| fun $funBinders* ($th : $(ctx.theoryT)) ($st0 : $(ctx.stateT)) ($lbl : $labelT) ($st1 : $(ctx.stateT)) =>
    (($(ctx.rtsExpr)).$(mkIdent `tr) $th $st0 $lbl $st1 : Prop))
  let fn ← Term.withoutErrToSorry do
    let fn ← elabTerm fnStx none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars fn
  if fn.hasSorry || fn.hasMVar || fn.hasLevelMVar then
    throwError "IC3: the transition relation of {ctx.mod.name} did not elaborate"
  let fnTy ← instantiateMVars (← inferType fn)
  let (c1, p1) ← simpContextOf (← `(tactic| simp only [$(mkIdent `nextSimp):ident]))
  let (c2, p2) ← simpContextOf (← `(tactic| simp only [↓ $(mkIdent ``Veil.existsQuantifierSimpGuarded):ident]))
  let (c3, p3) ← simpContextOf (← `(tactic| simp only [$(mkIdent `smtSimp):ident]))
  let normalize (e : Expr) : TermElabM Simp.Result := do
    let (r1, _) ← Meta.simp e c1 p1
    let (r2, _) ← Meta.simp r1.expr c2 p2
    let (r3, _) ← Meta.simp r2.expr c3 p3
    (← r1.mkEqTrans r2).mkEqTrans r3
  -- The definition: cases on the label, one normalized proposition per action.
  -- The proof of each case is kept, abstracted over the case's variables, for the theorem.
  let defMVar ← mkFreshExprMVar fnTy
  let (xs, g) ← defMVar.mvarId!.intros
  let lblFVar := xs[xs.size - 2]!
  let others := xs.filter (· != lblFVar)
  let body := (mkAppN fn (xs.map mkFVar)).headBeta
  let mut proofs : Array (Name × Expr) := #[]
  for sg in ← g.cases lblFVar do
    let pf ← sg.mvarId.withContext do
      let r ← normalize (sg.subst.apply body)
      sg.mvarId.assign r.expr
      let args := (others.map fun x => sg.subst.apply (mkFVar x)) ++ sg.fields
      mkLambdaFVars args (← r.getProof)
    proofs := proofs.push (sg.ctorName.getD .anonymous, pf)
  let defValue ← instantiateMVars defMVar
  addCheckedDecl (.defnDecl ⟨⟨name, [], fnTy⟩, defValue, .abbrev, .safe, [name]⟩)
  if failAt == some "afterDef" then
    throwError "injected failure, veil.synthesizer.debug.failNormalize afterDef"
  -- The theorem, by cases on the label; each case's type is the definition's
  -- case unfolded, which the kernel checks by unfolding.
  let thmTy ← instantiateMVars (← forallTelescope fnTy fun ys _ => do
    mkForallFVars ys (← mkEq (mkAppN fn ys).headBeta (mkAppN (mkConst name) ys)))
  let thmMVar ← mkFreshExprMVar thmTy
  let (ys, g) ← thmMVar.mvarId!.intros
  let lblY := ys[ys.size - 2]!
  let othersY := ys.filter (· != lblY)
  for sg in ← g.cases lblY do
    let some (_, pf) := proofs.find? (·.1 == sg.ctorName.getD .anonymous)
      | throwError "IC3: no normalized transition for constructor {sg.ctorName}"
    let args := (othersY.map fun y => sg.subst.apply (mkFVar y)) ++ sg.fields
    sg.mvarId.assign (pf.beta args)
  let eqValue ← instantiateMVars thmMVar
  addCheckedDecl (.thmDecl ⟨⟨eqName, [], thmTy⟩, eqValue, [eqName]⟩)
  return { mod := ctx.mod.name, defType := fnTy, defValue, eqType := thmTy, eqValue }

/-- How a run stood to the normalized transition relation, for the command's
report: built during the run; reused from an earlier run in the same module;
failed, so the queries were written with Veil's `tr`; off by
`veil.synthesizer.normalizeTr false`; or unused, because the run asked no two-state
question. -/
inductive TrNormStatus where
  | normalized | reused | failed | off | unused
deriving BEq, Repr

/-- The status as the `trNorm` field of the log's `outcome` event. -/
def TrNormStatus.key : TrNormStatus → String
  | .normalized => "normalized"
  | .reused => "reused"
  | .failed => "failed"
  | .off => "off"
  | .unused => "unused"

/-- The status of `mod` after a run; `builtBefore` says whether
`trNormAvailable` returned a name when the run started. -/
def trNormStatus (mod : Veil.Module) (builtBefore : Bool) : CoreM TrNormStatus := do
  unless veil.synthesizer.normalizeTr.get (← getOptions) do return .off
  if (← trNormFailed.get).contains mod.name then return .failed
  if (← trNormRecord? mod).isSome then return (if builtBefore then .reused else .normalized)
  return .unused

/-- Apply the conjunction of several state predicates to one state variable,
wrapped in a single theory/state binder. Veil's preprocessing pays for every
wrapper it has to destructure, so a frame of twenty clauses is asserted as one
conjunct rather than twenty. -/
def applyPreds (ctx : QueryCtx) (ts : Array Term) (st : Ident) (separate : Bool := false)
    : TermElabM (Array Term) := do
  if ts.isEmpty then return #[]
  if separate then return ← ts.mapM (ctx.applyPred · st)
  -- Capitals are quantified per conjunct, so two clauses using the same
  -- capital at different sorts do not share a binder.
  let conj ← repeatedAnd (← ts.mapM fun t => `(term| (uqc% (($t:term):Prop))))
  let w ← withTheoryAndStateFn ctx.mod conj (some (← `(term|Prop)))
    ctx.theoryT ctx.stateT ctx.fieldRepInstance ctx.stateSortTerm
  return #[← `(term| ($w $(ctx.th) $st))]

/-- `(⋁ₐ tag = a ∧ ic3_trNorm th stᵢ (Label.a args) stᵢ₊₁)` for transition
`trIdx` (1-based), plus the binders it introduces. `ic3_trNorm` is the
normalized transition relation (`ensureTrNorm`), equal to Veil's `tr`; when
the module has none, or with `plainTr`, the disjunct is written with `tr`.
The certificate asks an obligation in the plain form when its proof in the
normalized form could not be replayed (`Certificate.lean`). -/
def stepDisjunction (ctx : QueryCtx) (trIdx : Nat) (curr next : Ident) (plainTr : Bool := false)
    : TermElabM (Term × Array (TSyntax ``bracketedBinder)) := do
  -- A module without actions has no `ActionTag` type; its transition relation is empty.
  if ctx.mod.actions.isEmpty then return (← `(term| False), #[])
  let trNorm? ← if plainTr then pure none else ctx.ensureTrNorm
  let tagId := mkIdent (Name.mkSimple s!"_tr{trIdx}_tag")
  let mut binders : Array (TSyntax ``bracketedBinder) := #[← `(bracketedBinder| ($tagId : $actionTagType))]
  let mut disj : Array Term := #[]
  for act in ctx.mod.actions do
    let (_, specificParams) ← ctx.mod.declarationAllParams act.name act.declarationKind
    let mut args : Array Ident := #[]
    for i in [:specificParams.size] do
      let p := specificParams[i]!
      let id := mkIdent (Name.mkSimple s!"_tr{trIdx}_act_{act.name}_arg{i}_{p.name}")
      args := args.push id
      binders := binders.push (← `(bracketedBinder| ($id : $(p.type))))
    let tagMember := mkIdent (actionTagEnumInstName ++ act.name)
    let labelCtor := mkIdent (labelTypeName ++ act.name)
    let step ← match trNorm? with
      | some n => `(term| $(mkIdent n) $(ctx.sorts)* $(ctx.th) $curr ($labelCtor $args*) $next)
      | none => `(term| ($(ctx.rtsExpr)).$(mkIdent `tr) $(ctx.th) $curr ($labelCtor $args*) $next)
    disj := disj.push (← `(term| ($tagId = $tagMember ∧ $step)))
  return (← repeatedOr disj, binders)

/-- The universal statement `∀ binders (th) (st0 … stₖ), ¬ conj` with the
module's sort, typeclass and `ActionTag` binders in front. -/
def closeStatement (ctx : QueryCtx) (extraBinders : Array (TSyntax ``bracketedBinder))
    (numStates : Nat) (conj : Term) (withTags : Bool) : TermElabM Term := do
  let tagBinders : Array (TSyntax ``bracketedBinder) ← if withTags && !ctx.mod.actions.isEmpty then do
    pure #[← `(bracketedBinder| ($actionTagType : Type)),
           ← `(bracketedBinder| ($actionTagEnumInst : $(Ident.toEnumClass actionTagType) $actionTagType))]
    else pure #[]
  let binders := ctx.sortBinders ++ ctx.typeclassBinders ++ tagBinders ++ extraBinders
  let states := (Array.range numStates).map stateIdent
  `(∀ $binders* ($(ctx.th) : $(ctx.theoryT)) ($states* : $(ctx.stateT)), ¬ $conj)

/-- One-state query: `assumptions ∧ [init st0] ∧ ⋀ pre st0 ∧ ¬ post st0`. -/
def oneState (ctx : QueryCtx) (withInit : Bool) (pre : Array Term) (post : Term)
    (separate : Bool := false) : TermElabM Term := do
  let st0 := stateIdent 0
  let mut conj : Array Term := #[← `(term| ($(ctx.rtsExpr)).$(mkIdent `assumptions) $(ctx.th))]
  if withInit then conj := conj.push (← `(term| ($(ctx.rtsExpr)).$(mkIdent `init) $(ctx.th) $st0))
  conj := conj ++ (← ctx.applyPreds pre st0 separate)
  conj := conj.push (← `(term| ¬ $(← ctx.applyPred post st0)))
  ctx.closeStatement #[] 1 (← repeatedAnd conj) false

/-- Two-state query: `assumptions ∧ [init st0] ∧ ⋀ pre st0 ∧ tr st0 st1 ∧ ¬ post st1`.
With `separate`, each `pre` conjunct is its own hypothesis (the certificate
relies on that shape); by default they share one theory/state wrapper. With
`plainTr` the step is written with Veil's `tr` whatever the module has
(`stepDisjunction`). -/
def twoState (ctx : QueryCtx) (pre : Array Term) (post : Term) (withInit : Bool := false)
    (separate : Bool := false) (plainTr : Bool := false) : TermElabM Term := do
  let st0 := stateIdent 0
  let st1 := stateIdent 1
  let mut conj : Array Term := #[← `(term| ($(ctx.rtsExpr)).$(mkIdent `assumptions) $(ctx.th))]
  if withInit then conj := conj.push (← `(term| ($(ctx.rtsExpr)).$(mkIdent `init) $(ctx.th) $st0))
  conj := conj ++ (← ctx.applyPreds pre st0 separate)
  let (tr, binders) ← ctx.stepDisjunction 1 st0 st1 plainTr
  conj := conj.push tr
  conj := conj.push (← `(term| ¬ $(← ctx.applyPred post st1)))
  ctx.closeStatement binders 2 (← repeatedAnd conj) true

/-- Bounded path query: `assumptions ∧ init st0 ∧ ⋀ᵢ tr stᵢ stᵢ₊₁ ∧ ¬ post stₖ`
for `k` transitions. Used to tell a real counterexample from an abstract one. -/
def boundedPath (ctx : QueryCtx) (k : Nat) (post : Term) : TermElabM Term := do
  let mut conj : Array Term := #[← `(term| ($(ctx.rtsExpr)).$(mkIdent `assumptions) $(ctx.th)),
    ← `(term| ($(ctx.rtsExpr)).$(mkIdent `init) $(ctx.th) $(stateIdent 0))]
  let mut binders : Array (TSyntax ``bracketedBinder) := #[]
  for i in [:k] do
    let (tr, bs) ← ctx.stepDisjunction (i + 1) (stateIdent i) (stateIdent (i + 1))
    conj := conj.push tr
    binders := binders ++ bs
  conj := conj.push (← `(term| ¬ $(← ctx.applyPred post (stateIdent k))))
  ctx.closeStatement binders (k + 1) (← repeatedAnd conj) (k > 0)

/-- Like `twoState`, but the negated post-condition is a diagram given as
skolemized literals: extra binders `x0 … xₙ` (the diagram's elements) and one
conjunct per literal evaluated at `st1`. Each literal becomes its own
hypothesis after preprocessing, so an unsat core names the literals that
matter. `withInit` uses `init` in place of `pre` (frame 0). -/
def twoStateLits (ctx : QueryCtx) (pre : Array Term) (vars : Array SortName) (lits : Array Term)
    (withInit : Bool := false) (separate : Bool := false) : TermElabM Term := do
  let st0 := stateIdent 0
  let st1 := stateIdent 1
  let mut conj : Array Term := #[← `(term| ($(ctx.rtsExpr)).$(mkIdent `assumptions) $(ctx.th))]
  if withInit then conj := conj.push (← `(term| ($(ctx.rtsExpr)).$(mkIdent `init) $(ctx.th) $st0))
  conj := conj ++ (← ctx.applyPreds pre st0 separate)
  let (tr, binders) ← ctx.stepDisjunction 1 st0 st1
  conj := conj.push tr
  -- The literals share one wrapper (preprocessing pays per wrapper); the
  -- conjunction hypothesis is split into one hypothesis per literal after
  -- preprocessing, see `splitTrailingConjunction`.
  conj := conj ++ (← ctx.applyPreds lits st1)
  let varBinders ← (Array.range vars.size).mapM fun i =>
    `(bracketedBinder| ($(varIdent i) : $(mkIdent vars[i]!)))
  ctx.closeStatement (binders ++ varBinders) 2 (← repeatedAnd conj) true

/-- `assumptions ∧ init st0 ∧ ⋀ lits(st0)` with skolemized diagram variables. -/
def initLits (ctx : QueryCtx) (vars : Array SortName) (lits : Array Term) : TermElabM Term := do
  let st0 := stateIdent 0
  let mut conj : Array Term := #[← `(term| ($(ctx.rtsExpr)).$(mkIdent `assumptions) $(ctx.th)),
    ← `(term| ($(ctx.rtsExpr)).$(mkIdent `init) $(ctx.th) $st0)]
  conj := conj ++ (← ctx.applyPreds lits st0)
  let varBinders ← (Array.range vars.size).mapM fun i =>
    `(bracketedBinder| ($(varIdent i) : $(mkIdent vars[i]!)))
  ctx.closeStatement varBinders 1 (← repeatedAnd conj) false

end QueryCtx

/-- Veil's `veil_bmc` preprocessing, without the final solver call: the goal is
massaged into first-order hypotheses that `smt` can translate. `trNorm` is
the module's normalized transition relation when it has one
(`QueryCtx.ensureTrNorm`): it is unfolded after the first two `simp` passes,
which then do not traverse the action bodies, and before `veil_intros`, so
that the rest of the pipeline sees the statement it saw when the relation was
`tr`. -/
def preprocessTactic (trNorm : Option Name) (trust : Bool) : TermElabM (TSyntax `tactic) := do
  let inferNonempty ← if trust then `(tactic| skip) else `(tactic| veil_infer_nonempty)
  let unfoldNorm ← match trNorm with
    | some n => `(tactic| try dsimp only [$(mkIdent n):ident])
    | none => `(tactic| skip)
  let dsimpLemmas := #[mkIdent ``Inhabited.default, fieldAbstractDispatcher,
    fieldLabelToDomain stateName, fieldLabelToCodomain stateName]
  let dsimpTac ← `(tactic| try dsimp +$(mkIdent `instances) [$[$dsimpLemmas:ident],*])
  let nextSimp := mkIdent `nextSimp
  let smtSimp := mkIdent `smtSimp
  let exq := mkIdent ``Veil.existsQuantifierSimpGuarded
  `(tactic| ($inferNonempty:tactic; veil_simp +$(mkIdent `instances) only [$nextSimp:ident]; veil_simp +$(mkIdent `instances) only [↓ $exq:ident]; $unfoldNorm:tactic; veil_intros; $inferNonempty:tactic; veil_destruct; $dsimpTac:tactic; veil_simp +$(mkIdent `instances) only [$smtSimp:ident]; $dsimpTac:tactic))

/-- The `smt` call Veil's `veil_smt` makes. Models are produced only when
`wantModel` is set. lean-smt no longer minimizes models (it was off here, as
in Veil: finite-model finding already returns minimal sort sizes, relation
minimization cannot shrink a diagram, and it was measured to cost more than it
saved, running past the per-query timeout on one four-element model). -/
def smtTactic (hyps : Array Ident) (trust : Bool) (timeout : Nat) (fmf : Bool) (wantModel : Bool := true)
    : TermElabM (TSyntax `tactic) := do
  let modelFlag := mkIdent <| if wantModel then ``true else ``false
  let fmfValue := if fmf then "true" else "false"
  let trustValue := mkIdent <| if trust then ``true else ``false
  let trustValueNegated := mkIdent <| if trust then ``false else ``true
  let solverOptions ← `(term| [("finite-model-find", $(Syntax.mkStrLit fmfValue)), ("nl-ext-tplanes", "true"), ("enum-inst-interleave", "true")])
  let smtTac ← `(tactic|
    smt
      ($(mkIdent `trust):ident := $trustValue:ident)
      ($(mkIdent `embedBool):ident := $trustValueNegated:ident)
      ($(mkIdent `model):ident := $modelFlag:ident)
      ($(mkIdent `timeout):ident := $(mkIdent ``Option.some) $(quote timeout))
      ($(mkIdent `extraSolverOptions):ident := $solverOptions)
      [$[$hyps:ident],*])
  `(tactic| open $(mkIdent `Classical):ident in $smtTac:tactic)

/-- Hypotheses to hand to the solver: propositions that are not typeclass
facts, in context order. Mirrors Veil's `getPropsInContext`. -/
def solverHyps (g : MVarId) : MetaM (Array LocalDecl) := g.withContext do
  let mut out := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← whnf decl.type
    if ty.isAppOf ``Nonempty || ty.isAppOf ``Inhabited then continue
    unless ← Meta.isProp ty do continue
    out := out.push decl
  return out

/-- Split a hypothesis `h : A ∧ (B ∧ …)` into one hypothesis per conjunct,
left to right, so that each conjunct of a query is its own solver hint. -/
partial def splitConjunction (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← h.getType)
  if ty.isAppOfArity ``And 2 then
    let subgoals ← g.cases h
    match subgoals with
    | #[sub] =>
      match sub.fields with
      | #[l, r] =>
        let g₁ ← splitConjunction sub.mvarId l.fvarId!
        splitConjunction g₁ r.fvarId!
      | _ => return sub.mvarId
    | _ => return g
  else
    return g

/-- If the last hypothesis is a conjunction (the diagram literals asserted
under one wrapper), split it into one hypothesis per conjunct, in order, so
that the literals are again the last `k` hypotheses. -/
def splitTrailingConjunction (g : MVarId) : MetaM MVarId := g.withContext do
  let mut last : Option LocalDecl := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← Meta.isProp decl.type then last := some decl
  match last with
  | some decl =>
    if (← whnfR decl.type).isAppOfArity ``And 2 then splitConjunction g decl.fvarId else return g
  | none => return g

/-- Unfold every `CanonicalField D T` of the goal and its hypotheses to the
type it abbreviates (`T` for an individual, `D₁ → … → T` otherwise), a
definitional change. Veil elaborates an expression assigned to a field at the
field's type, so `total := total + 1` on an `Int` individual gives
`@HAdd.hAdd Int (CanonicalField [] Int) Int _ total (@OfNat.ofNat
(CanonicalField [] Int) 1 _)`, and lean-smt, which translates type arguments as
written, fails on it with "cannot translate Type". -/
def unfoldCanonicalFields (g : MVarId) : MetaM MVarId := g.withContext do
  let unfold (e : Expr) : MetaM Expr := Meta.transform e (post := fun e => do
    if e.isAppOfArity ``Veil.CanonicalField 2 || e.isAppOfArity ``Veil.IteratedArrow 2 then
      let e' ← whnfR e
      if e' != e then return .visit e'
    return .continue)
  let mut g ← g.replaceTargetDefEq (← unfold (← g.getType))
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← unfold decl.type
    if ty != decl.type then g ← g.replaceLocalDeclDefEq decl.fvarId ty
  return g

/-- If the goal is `¬ C` (or `C → False`), introduce `C` and split it. -/
def introAndSplit (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← g.getType)
  if ty.isAppOfArity ``Not 1 || ty.isArrow then
    let (h, g') ← g.intro1
    splitConjunction g' h
  else
    return g

/-- Whether the search may take the solver's `unsat` answers on faith. Off by
default: lean-smt reconstructs every answer as a Lean proof term. The search
does not send those terms to the kernel; `certify` asks every obligation again
and adds its proof only after the kernel accepts it. Certificates reconstruct
whatever this says. Veil's own
`veil.smt.trust` is not consulted, so a module's setting of that option does
not weaken the synthesizer. -/
register_option veil.synthesizer.trust : Bool := {
  defValue := false
  descr := "let the IC3 search take the solver's unsat answers on faith instead of reconstructing proofs (certificates always reconstruct)"
}

/-- A fault hook for the regression tests: every query over `k` transitions
fails in the way the value names. `"unknown:k"` answers `unknown` without
asking the solver; `"undecoded:k"` takes a `sat` answer's model as one that
did not decode; `"throw:k"` throws once the statement is elaborated, as a bug
in the query pipeline would. `k` is the number of transitions of the statement (`0` for
`init ∧ ¬P`, `1` for the frontier and predecessor queries, `N + 1` for the
bounded path check of an abstract counterexample rooted at level 0), so a
test can make one question of the search fail and no other. The empty
string, the default, is off; any other value is an error (`failQueryAt`). -/
register_option veil.synthesizer.debug.failQuery : String := {
  defValue := ""
  descr := "make every query over k transitions fail, for tests: \"unknown:k\" answers unknown without asking the solver, \"undecoded:k\" takes a sat answer's model as one that did not decode, \"throw:k\" throws once the statement is elaborated"
}

/-- The failure and transition count `veil.synthesizer.debug.failQuery` names, or an error
for a value it does not define. `#synthesize_invariants` reads it before the
run, as it does `veil.synthesizer.debug.failNormalize`. -/
def failQueryAt : CoreM (Option (String × Nat)) := do
  let v := veil.synthesizer.debug.failQuery.get (← getOptions)
  if v.isEmpty then return none
  match v.splitOn ":" with
  | [kind, k] =>
    if let some n := k.toNat? then
      if ["unknown", "undecoded", "throw"].contains kind then return some (kind, n)
  | _ => pure ()
  throwError "IC3: veil.synthesizer.debug.failQuery is \"{v}\"; its values are \"unknown:k\", \"undecoded:k\" and \"throw:k\" for a number of transitions k"

/-- The message of a failure injected by `veil.synthesizer.debug.failQuery`. -/
def injectedQueryFailure (kind : String) (k : Nat) : String :=
  s!"injected failure, veil.synthesizer.debug.failQuery {kind}:{k}"

/-- Heartbeat budget for one query. The count restarts at the query
(`withCurrHeartbeats`); without that the budget would be measured from the
start of the enclosing command. -/
private def queryBudget : {α : Type} → TermElabM α → TermElabM α := fun x =>
  withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := 4000000 * 1000 }) x

/-- Discharge a closed statement: preprocess, call the solver, collect the
outcome. If `numTrailingLits > 0`, the statement's last that many conjuncts are
diagram literals, and on `unsat` the indices of those literals that appear in
the unsat core are returned as well (`none` when they could not be identified).
`numTransitions` is needed to decode a `sat` model.

Unsat cores are only available on lean-smt's proof-reconstruction path, so a
query that asks for literal cores runs with reconstruction whatever
`veil.synthesizer.trust` says; when its answer cannot be read, `runStatementCore` asks
the statement again without cores, under `veil.synthesizer.trust` as set. -/
private def runStatementBody (mod : Veil.Module) (stmt : Term) (numTransitions : Nat)
    (numTrailingLits : Nat) (wantModel : Bool) : TermElabM (QueryResult × Option (Array Nat)) := do
  let opts ← getOptions
  let fault ← failQueryAt
  let trust := veil.synthesizer.trust.get opts && numTrailingLits == 0
  let timeout := veil.smt.timeout.get opts
  let fmf := veil.smt.finiteModelFind.get opts
  let ch ← Std.CloseableChannel.new
  let name ← mkFreshUserName `synthQuery
  let _ ← Smt.initAsyncState name (some ch)
  -- A statement that does not elaborate must not be solved with `sorry` in
  -- it: fail the query instead.
  let tElab ← IO.monoMsNow
  let ty? : Except String Expr ← try
      let ty ← Term.withoutErrToSorry do
        let ty ← elabTerm stmt (some (mkSort .zero))
        synthesizeSyntheticMVarsNoPostponing
        instantiateMVars ty
      if ty.hasSorry || ty.hasMVar || ty.hasLevelMVar then pure (Except.error "statement contains sorry or metavariables")
      else pure (Except.ok ty)
    catch e => pure (Except.error (← e.toMessageData.toString))
  notePhase (fun p dt => { p with elabMs := p.elabMs + dt }) tElab
  let ty : Expr ← match ty? with
    | Except.ok ty => pure ty
    | Except.error e => return (QueryResult.error s!"statement failed to elaborate: {e.take 300}", none)
  if fault == some ("throw", numTransitions) then throwError (injectedQueryFailure "throw" numTransitions)
  let mv ← mkFreshExprMVar ty
  -- Preprocessing can be expensive on big frames; an overrun of the query
  -- budget is reported as `unknown`. Runtime exceptions need `tryCatchRuntimeEx`.
  let tPre ← IO.monoMsNow
  let trNorm ← QueryCtx.trNormAvailable mod
  let goals? : Except String (List MVarId) ← tryCatchRuntimeEx
    (do
      let gs ← Lean.Elab.Tactic.run mv.mvarId! (Lean.Elab.Tactic.evalTactic (← preprocessTactic trNorm trust))
      pure (.ok gs))
    (fun e => do pure (.error (← e.toMessageData.toString)))
  notePhase (fun p dt => { p with preprocessMs := p.preprocessMs + dt }) tPre
  let goals ← match goals? with
    | .ok gs => pure gs
    | .error e => return (QueryResult.unknown s!"preprocessing failed: {e.take 300}", none)
  match goals with
  | [] =>
    -- Preprocessing alone closed the goal: the conjunction is contradictory.
    let pf ← instantiateMVars mv
    return (QueryResult.unsat ty pf (pf.hasSorry || pf.hasMVar), some #[])
  | g₀ :: _ =>
    let g ← introAndSplit g₀
    let g ← if numTrailingLits > 0 then splitTrailingConjunction g else pure g
    let g ← unfoldCanonicalFields g
    let hyps ← solverHyps g
    let litHyps : Array FVarId := if numTrailingLits > 0 && hyps.size ≥ numTrailingLits
      then (hyps.extract (hyps.size - numTrailingLits) hyps.size).map (·.fvarId) else #[]
    if numTrailingLits > 0 && (← isTracingEnabledFor `veil.synthesizer.debug) then
      g.withContext do
        let mut msg := m!"{hyps.size} solver hypotheses for {numTrailingLits} literals; goal: {← g.getType}\n"
        for d in hyps do msg := msg ++ m!"  {d.userName} : {d.type}\n"
        logInfo msg
    let idents := hyps.map fun d => mkIdent d.userName
    let smtTac ← smtTactic idents trust timeout fmf wantModel
    let tSmt ← IO.monoMsNow
    -- Proof reconstruction may leave "trust" goals for steps lean-smt cannot
    -- reconstruct; they are admitted here so the proof term carries `sorry`
    -- and the result is reported as trusted.
    let solveErr? : Option String ← tryCatchRuntimeEx
      (do
        let remaining ← Lean.Elab.Tactic.run g (Lean.Elab.Tactic.evalTactic smtTac)
        for r in remaining do r.admit (synthetic := false)
        pure none)
      (fun e => do pure (some (← e.toMessageData.toString)))
    let outputs ← collectSmtOutputs ch name
    notePhase (fun p dt => { p with smtMs := p.smtMs + dt }) tSmt
    -- lean-smt reports `unknown` (timeouts included) by throwing after the
    -- `smt` call returns, so nothing arrives on the channel and the message
    -- has to be classified here. Only `unsat`, `sat` and exceptions are sent.
    let mut result : QueryResult := match solveErr? with
      | some e =>
        if (e.splitOn "unable to prove goal. Try providing more hints. Reason:").length > 1
          || (unknownExplanation? e).isSome
        then QueryResult.unknown s!"{solverUnknownPrefix}: {e.take 300}"
        else QueryResult.error s!"solver produced no output: {e.take 300}"
      | none => QueryResult.error "solver produced no output"
    let mut core : Option (Array Nat) := none
    for o in outputs do
      match o with
      | (_, Smt.AsyncOutput.result (Smt.Result.sat none)) =>
        -- Asked without a model: `sat` is the whole answer.
        result := if wantModel then QueryResult.satUndecoded "the solver returned no model" else QueryResult.sat Json.null
      | (_, Smt.AsyncOutput.result (Smt.Result.sat (some m))) =>
        let tDecode ← IO.monoMsNow
        result ← if fault == some ("undecoded", numTransitions) then
            pure (QueryResult.satUndecoded (injectedQueryFailure "undecoded" numTransitions))
          else
            tryCatchRuntimeEx
              (do let vt ← buildTraceFromModel m mod numTransitions; pure (QueryResult.sat (← unsafe vt.toJson)))
              (fun e => do pure (QueryResult.satUndecoded s!"{(← e.toMessageData.toString).take 300}"))
        notePhase (fun p dt => { p with decodeMs := p.decodeMs + dt }) tDecode
      | (_, Smt.AsyncOutput.result (Smt.Result.unsat _ used)) =>
        let pf ← instantiateMVars mv
        result := QueryResult.unsat ty pf (pf.hasSorry || pf.hasMVar)
        if numTrailingLits > 0 && litHyps.size == numTrailingLits then
          let usedIds := used.filterMap fun e => if e.isFVar then some e.fvarId! else none
          core := some <| (Array.range numTrailingLits).filter fun i => usedIds.contains litHyps[i]!
      | (_, Smt.AsyncOutput.exception e) =>
        let msg ← e.toMessageData.toString
        result := if (unknownExplanation? msg).isSome then QueryResult.unknown s!"{solverUnknownPrefix}: {msg}" else QueryResult.error msg
      | _ => pure ()
    return (result, core)

/-- Run `x`, then put lean-smt's async state back as it was. `runStatementBody`
installs its query's channel there; left in place, the channel would outlive
the command and receive the output of a later `smt` call in the same file. -/
private def restoringSmtAsyncState (x : TermElabM α) : TermElabM α := do
  let saved := Smt.asyncState.getState (← getEnv)
  try x finally modifyEnv (Smt.asyncState.modifyState · fun _ => saved)

/-- `runStatementBody` under the per-query heartbeat budget, every phase
included (elaboration, preprocessing, solving, decoding); an overrun anywhere
(a heartbeat or recursion-depth exception) is `unknown`. Any other exception
the phases do not catch themselves is a bug in this pipeline, not a solver
limit, and is rethrown: the search reports it as an internal error and a
certificate as an error of the command. When the answer of a core query cannot be read (an error result
other than an elaboration failure: a reconstruction exception, most often),
the statement is asked again without cores, under `veil.synthesizer.trust` as set:
Algorithm 2 needs only the verdict, the core is an optimization of the
generalization step. -/
def runStatementCore (mod : Veil.Module) (stmt : Term) (numTransitions : Nat) (numTrailingLits : Nat)
    (wantModel : Bool := true) : TermElabM (QueryResult × Option (Array Nat)) := do
  if (← failQueryAt) == some ("unknown", numTransitions) then
    return (.unknown (injectedQueryFailure "unknown" numTransitions), none)
  let run (lits : Nat) : TermElabM (QueryResult × Option (Array Nat)) :=
    queryBudget <| tryCatchRuntimeEx
      (restoringSmtAsyncState (runStatementBody mod stmt numTransitions lits wantModel))
      (fun e => do
        unless e.isRuntime do throw e
        pure (QueryResult.unknown s!"query exceeded its budget: {(← e.toMessageData.toString).take 200}", none))
  let r ← run numTrailingLits
  let r ← match r with
    | (.error e, _) =>
      -- An elaboration failure would repeat; anything else may succeed without cores.
      if numTrailingLits > 0 && !e.startsWith "statement failed to elaborate" then run 0 else pure r
    | _ => pure r
  match r with
  | (.error e, _) =>
    -- The solver answered but lean-smt could not replay its proof (integer
    -- proofs that pass through real arithmetic are the usual case). The answer
    -- is as good as any trusted one: ask once more trusting the solver, so the
    -- verdict is `unsat` marked `viaTrust`. The certificate re-proves every
    -- clause with reconstruction and reports what could not be replayed.
    if !(veil.synthesizer.trust.get (← getOptions)) && (e.splitOn "Failed to reconstruct").length > 1 then
      withOptions (fun o => veil.synthesizer.trust.set o true) (run 0)
    else pure r
  | _ => pure r

/-- Discharge a statement. `wantModel := false` skips model production for
queries whose `sat` answer is used only as a verdict. -/
def runStatement (mod : Veil.Module) (stmt : Term) (numTransitions : Nat) (wantModel : Bool := true)
    : TermElabM QueryResult :=
  (·.1) <$> runStatementCore mod stmt numTransitions 0 wantModel

end Veil.Synthesizer
