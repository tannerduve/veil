module

public meta import Veil
public meta import Veil.Core.Tools.Synthesizer.Controller
public meta import Veil.Core.Tools.Synthesizer.Certificate
public meta import Veil.Core.Tools.Synthesizer.Counterexample

/-!
# `#synthesize_invariants`

Runs UPDR on the current Veil module's `safety` clauses (and, with
`(invariants := true)`, its declared `invariant`s) and prints the outcome:
strengthening clauses ready to paste into the module as `invariant [ic3_k] …`
declarations, a concrete counterexample, an abstract counterexample showing
that no universal invariant exists (a verdict, not a Lean theorem), or the
reason the search stopped.

Options may appear in any order, each at most once:
`#synthesize_invariants (fuel := 500) (log := "run.jsonl") (invariants := true) verbose certify`,
`#synthesize_invariants (expect := unsafe)` for a module with a planted bug.
-/

public meta section

namespace Veil.Synthesizer
open Lean Elab Command Term Meta Veil

register_option veil.synthesizer.timings : Bool := {
  defValue := false
  descr := "report separate wall times for IC3 synthesis and kernel certification"
}

private def reportPhaseTime (phase : String) (started : Nat) : CommandElabM Unit := do
  if veil.synthesizer.timings.get (← getOptions) then
    logInfo s!"IC3 timing {phase}: {(← IO.monoMsNow) - started} ms"

syntax synthFuel := &"fuel" " := " num
syntax synthLog := &"log" " := " str
syntax synthExpectKind := &"invariant" <|> &"unsafe" <|> &"no_universal_invariant" <|> &"unknown"
syntax synthExpect := &"expect" " := " synthExpectKind
syntax synthInvariants := &"invariants" " := " (&"true" <|> &"false")
syntax synthGeneralizer := &"generalizer" " := " (&"updr" <|> &"linear")
syntax synthCores := &"cores" " := " (&"true" <|> &"false")
syntax synthOpt := "(" (synthFuel <|> synthLog <|> synthExpect <|> synthInvariants <|> synthGeneralizer <|> synthCores) ")"
syntax (name := synthesizeInvariants) "#synthesize_invariants" (synthOpt <|> &"verbose" <|> &"certify")* : command

/-- The verdict a test expects from the command (`(expect := …)`). -/
inductive Expectation where
  | invariant | «unsafe» | noUniversalInvariant | unknown
deriving BEq, Repr

def Expectation.describe : Expectation → String
  | .invariant => "an inductive invariant"
  | .«unsafe» => "a counterexample"
  | .noUniversalInvariant => "the no-universal-invariant verdict"
  | .unknown => "a stopped run"

def Expectation.matches : Expectation → Outcome → Bool
  | .invariant, .foundInvariant .. => true
  | .«unsafe», .«unsafe» _ => true
  | .noUniversalInvariant, .noUniversalInvariant .. => true
  | .unknown, .unknown .. => true
  | .unknown, .absenceWithheld .. => true
  | _, _ => false

def Outcome.describe : Outcome → String
  | .foundInvariant .. => "an inductive invariant"
  | .«unsafe» _ => "a counterexample"
  | .unsafeUndecoded .. => "a violation whose execution could not be decoded"
  | .noUniversalInvariant .. => "the no-universal-invariant verdict"
  | .unknown .. => "a stopped run"
  | .absenceWithheld .. => "a stopped run"
  | .internalError .. => "an internal error"

/-- The `outcome` field of the log file's `outcome` event. -/
def outcomeJson : Outcome → Json
  | .foundInvariant frame clauses _ => Json.mkObj [("kind", "invariant"), ("frame", (frame : Nat)),
      ("clauses", toJson (clauses.map fun a => clauseJson a.clause))]
  | .«unsafe» p => Json.mkObj [("kind", "unsafe"), ("steps", (p.states.size - 1 : Nat))]
  | .unsafeUndecoded k r => Json.mkObj [("kind", "unsafe"), ("steps", k), ("reason", r)]
  | .noUniversalInvariant ds _ => Json.mkObj [("kind", "no_universal_invariant"), ("diagrams", (ds.size : Nat))]
  | .absenceWithheld ds _ _ => Json.mkObj [("kind", "unknown"), ("reason", absenceWithheldReason), ("diagrams", (ds.size : Nat))]
  | .unknown r _ => Json.mkObj [("kind", "unknown"), ("reason", r)]
  | .internalError m _ => Json.mkObj [("kind", "internal_error"), ("message", m)]

/-- Render a state as `symbol: {tuples}` lines. A Boolean individual or a
0-ary class predicate prints as `true` or `false`; a relation as its tuples,
`∅` when empty; a function as `args ↦ value` rows, a constant as its value.
Elements of an enum sort print as their constructors, an enum sort as its
constructor list. -/
private def renderState (σ : FinStructure) : String :=
  let sorts := String.intercalate ", " (σ.sorts.toList.map fun (s, n) =>
    match σ.enums.find? (·.1 == s) with
    | some (_, ctors) => s!"{s} = \{{String.intercalate ", " (ctors.toList.map toString)}}"
    | none => s!"{s} = Fin {n}")
  let els (sym : RelSym) (t : Array Nat) : List String :=
    ((sym.argSorts.zip t).map fun (s, i) => σ.elementName s i).toList
  let rels := σ.rels.toList.map fun (sym, tuples) =>
    let table :=
      if sym.isFunction then
        String.intercalate " " (tuples.toList.map fun t =>
          let names := els sym t
          let value := names.getLast?.getD "?"
          let args := names.dropLast
          if args.isEmpty then value else "(" ++ String.intercalate "," args ++ ")↦" ++ value)
      else if sym.argSorts.isEmpty then (if tuples.isEmpty then "false" else "true")
      else if tuples.isEmpty then "∅"
      else String.intercalate " " (tuples.toList.map fun t => "(" ++ String.intercalate "," (els sym t) ++ ")")
    s!"    {sym.key}: {table}"
  let nums := σ.nums.toList.map fun (sym, table) =>
    let rows := table.toList.map fun (t, v) =>
      let args := ((sym.argSorts.pop.zip t).map fun (s, i) => σ.elementName s i).toList
      if args.isEmpty then toString v else "(" ++ String.intercalate "," args ++ ")↦" ++ toString v
    s!"    {sym.key}: {String.intercalate " " rows}"
  s!"    sorts: {sorts}\n" ++ String.intercalate "\n" (rels ++ nums)

/-- The action name in a decoded transition label (`{"act": {…}}` or `"act"`). -/
private def actionOfLabel (j : Json) : Option String :=
  match j with
  | .str s => some s
  | .obj kvs => match kvs.toArray with
    | #[(k, _)] => some k
    | _ => none
  | _ => none

/-- Milliseconds as `s.d` seconds. -/
private def seconds (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

/-- Strengthening-clause counts per frame, for the stopped and error messages. -/
private def frameSummary (sizes : Array Nat) : String :=
  if sizes.isEmpty then "no frame opened"
  else s!"{sizes.size} frame(s) opened; strengthening clauses per frame F₁ … F_{sizes.size}: {sizes}"

/-- What the structures of an abstract counterexample are, for its messages. -/
private def chainDescription : String :=
  "the first is contained in an initial state, each next in a successor of a state containing the previous, and a successor of a state containing the last violates the property"

/-- The line after "Certified": what the theorem's axioms say. -/
private def certificateStatus (cert : CertificateResult) : String :=
  if cert.kernelChecked then "kernel-checked, standard axioms only"
  else
    let note := if cert.offenders.contains ``sorryAx then "; sorryAx means a solver step could not be replayed as a Lean proof (lean-smt could not reconstruct it, or the kernel rejected its reconstruction)" else ""
    s!"depends on {cert.offenders} beyond the standard axioms{note}"

@[command_elab synthesizeInvariants]
def elabSynthesizeInvariants : CommandElab := fun stx => do
  let mod ← getCurrentModule (errMsg := "#synthesize_invariants must be used inside a Veil module")
  mod.throwIfSpecNotFinalized
  let mut fuel : Nat := ({} : Config).fuel
  let mut logFile : Option System.FilePath := none
  -- `(expect := …)` turns the expected verdict into a plain message and any
  -- other outcome into an error, for regression tests.
  let mut expectation : Option Expectation := none
  let mut useDeclaredInvariants := false
  let mut generalizer : GeneralizerKind := .linear
  let mut cores := true
  let mut verbose := false
  let mut doCertify := false
  let mut seen : Array String := #[]
  for arg in stx[1].getArgs do
    let inner := if arg.isOfKind ``synthOpt then arg[1] else arg
    let mut key := ""
    -- A bare flag parses as a `token.<flag>` node around the atom.
    let flag? : Option String := match inner with
      | .atom _ v => some v
      | .node _ _ #[.atom _ v] => some v
      | _ => none
    if let some flag := flag? then
      key := flag
      match flag with
      | "verbose" => verbose := true
      | "certify" => doCertify := true
      | _ => throwErrorAt arg "unknown option"
    else
      match inner with
      | `(synthFuel| fuel := $n:num) => key := "fuel"; fuel := n.getNat
      | `(synthLog| log := $s:str) =>
        key := "log"
        let path := s.getString
        if path.isEmpty then throwErrorAt s "the log file path is empty"
        logFile := some (System.FilePath.mk path)
      | `(synthExpect| expect := invariant) => key := "expect"; expectation := some .invariant
      | `(synthExpect| expect := unsafe) => key := "expect"; expectation := some .«unsafe»
      | `(synthExpect| expect := no_universal_invariant) => key := "expect"; expectation := some .noUniversalInvariant
      | `(synthExpect| expect := unknown) => key := "expect"; expectation := some .unknown
      | `(synthInvariants| invariants := true) => key := "invariants"; useDeclaredInvariants := true
      | `(synthInvariants| invariants := false) => key := "invariants"; useDeclaredInvariants := false
      | `(synthGeneralizer| generalizer := updr) => key := "generalizer"; generalizer := .updr
      | `(synthGeneralizer| generalizer := linear) => key := "generalizer"; generalizer := .linear
      | `(synthCores| cores := true) => key := "cores"; cores := true
      | `(synthCores| cores := false) => key := "cores"; cores := false
      | _ => throwErrorAt arg "unknown option"
    if seen.contains key then throwErrorAt arg "the option {key} is given twice"
    seen := seen.push key
  let cfg : Config := { fuel, verbose, logFile, useDeclaredInvariants, generalizer, cores }
  -- Rejections first: a module outside the supported shapes, or without a
  -- property, gets its error and no message about a run. The vocabulary is
  -- computed once here, for the search and for the verdict messages.
  let sig ← liftTermElabM (Signature.ofModule mod)
  let property ← liftCoreM (checkedProperty mod cfg)
  -- A value of a fault hook it does not define is an error of the command.
  let _ ← liftCoreM QueryCtx.failNormalizeAt
  let _ ← liftCoreM failQueryAt
  -- What the verdict is about: the `safety` clauses, those plus the declared
  -- invariants, or the declared invariants alone when the module has no `safety`.
  let propertyName :=
    if mod.safeties.isEmpty then "the declared invariants"
    else if useDeclaredInvariants then "the safety property together with the declared invariants"
    else "the safety property"
  -- The transition system does not assume `trusted invariant`s; a refutation
  -- may run through states they exclude.
  let trustedNote := if mod.trustedInvariants.isEmpty then "" else " (trusted invariants were not assumed)"
  -- A module holds one certificate; refuse before the search rather than after.
  if doCertify then throwIfCertified mod [`ic3_prop, `ic3_safe, `ic3_unsafe, `ic3_init_0]
  -- The names of the normalized transition relation are reserved as well; a
  -- declaration of another origin under them is refused, not used.
  liftCoreM (QueryCtx.throwIfTrNormForeign mod)
  let trNormBefore := (← liftCoreM (QueryCtx.trNormAvailable mod)).isSome
  -- Initial states of the transition system keep `default` for these
  -- components; `#check_invariants` proves initiation from any pre-state.
  let unassigned := Signature.unassignedByInit mod
  unless unassigned.isEmpty do
    logWarning s!"IC3: after_init does not assign {", ".intercalate (unassigned.map toString).toList}; the certificate's initial states keep the default value of these components, and #check_invariants may reject a clause that relies on it (see \"Semantics\" in docs/Invariant-Synthesis.md)"
  let synthesisStarted ← IO.monoMsNow
  let result ← liftTermElabM <| synthesize mod cfg sig
  reportPhaseTime "synthesis" synthesisStarted
  let outcome := result.outcome
  let stats := result.stats
  let ph := stats.phases
  -- What the run did about the normalized transition relation.
  let trNormStatus ← liftCoreM (QueryCtx.trNormStatus mod trNormBefore)
  let trNormNote := match trNormStatus with
    | .normalized => s!"; transition relation normalized once in {seconds ph.normalizeMs} s"
    | .reused => "; transition relation reused from an earlier run in this module"
    | .failed => s!"; transition relation not normalized{if ph.normalizeMs > 0 then s!" ({seconds ph.normalizeMs} s spent on the attempt)" else ""}, the queries were written with Veil's `tr`"
    | .off => "; transition relation not normalized (veil.synthesizer.normalizeTr false)"
    | .unused => ""
  logInfo s!"solver calls: {stats.solverCalls}, {seconds stats.solverMs} s (preprocessing {seconds ph.preprocessMs} s, elaboration {seconds ph.elabMs} s, solving {seconds ph.smtMs} s, decoding {seconds ph.decodeMs} s){trNormNote}"
  if let some path := cfg.logFile then
    try
      appendEvent path <| Json.mkObj [("event", "outcome"), ("module", toString mod.name),
        ("solverCalls", (stats.solverCalls : Nat)), ("solverMs", (stats.solverMs : Nat)),
        ("preprocessMs", (ph.preprocessMs : Nat)), ("elabMs", (ph.elabMs : Nat)), ("smtMs", (ph.smtMs : Nat)),
        ("decodeMs", (ph.decodeMs : Nat)), ("normalizeMs", (ph.normalizeMs : Nat)), ("trNorm", trNormStatus.key),
        ("outcome", outcomeJson outcome)]
    catch e => logWarning m!"IC3: could not append the outcome to the log file {path}: {e.toMessageData}"
  -- `expected` says the outcome is the one a test asked for: it is then
  -- reported as information, whatever its usual severity.
  let expected := match expectation with
    | some e => e.matches outcome
    | none => false
  if let some e := expectation then
    unless e.matches outcome do
      logError s!"expected {e.describe}, got {outcome.describe}"
  match outcome with
  | .foundInvariant frame clauses anyTrusted =>
    -- Under `veil.synthesizer.trust true` every answer is taken on faith; under the
    -- default an answer is trusted only when lean-smt could not replay its
    -- proof (`runStatementCore`).
    let trusting := veil.synthesizer.trust.get (← getOptions)
    let trustNote := if !anyTrusted then " (lean-smt reconstructed every solver answer of the search as a proof term; the search does not kernel-check those terms, `certify` does)"
      else if trusting then " (the search took the solver's answers on faith under `veil.synthesizer.trust true`; a certificate reconstructs its own proofs)"
      else " (the search took some solver answers on faith because lean-smt could not replay their proofs; a certificate reconstructs its own proofs and reports what it cannot)"
    if clauses.isEmpty then
      logInfo s!"Inductive invariant found at frame {frame}: the property is inductive on its own{trustNote}"
    else
      let mut msg := s!"Inductive invariant found at frame {frame} with {clauses.size} strengthening clause(s){trustNote}:\n"
      let mut k := 0
      for a in clauses do
        msg := msg ++ s!"invariant [ic3_{k}] {a.clause}\n"
        k := k + 1
      logInfo msg
    if doCertify then
      let certificationStarted ← IO.monoMsNow
      let cert ← certify mod property (clauses.map (·.clause))
      reportPhaseTime "certification" certificationStarted
      logInfo s!"Certified: theorem {cert.theoremName} (strengthening {cert.strengtheningName}); axioms: {cert.axioms}; {certificateStatus cert}"
  | .«unsafe» path =>
    let mut msg := s!"Violated: {propertyName}{trustedNote}. Execution of {path.states.size - 1} step(s):\n"
    for i in [:path.states.size] do
      msg := msg ++ s!"  state {i}:\n{renderState path.states[i]!}\n"
      if i + 1 < path.states.size then msg := msg ++ s!"  step: {path.labels[i+1]!}\n"
    -- The same execution as a Veil trace specification, so it can be re-checked
    -- independently with `sat trace`. Each conjunct is wrapped in `uqc%` so
    -- that its capitals are quantified inside the negation, as the controller
    -- quantified them.
    let actNames := (path.labels.toList.drop 1).map fun l => (actionOfLabel l).getD "any action"
    let propTexts ← liftCoreM <| property.toList.mapM fun t => do
      pure s!"(uqc% ({← PrettyPrinter.ppTerm t}))"
    let propText := String.intercalate " ∧ " propTexts
    msg := msg ++ "Re-check with:\n  sat trace [ic3_cex] {\n" ++
      String.intercalate "" (actNames.map fun a => s!"    {a}\n") ++
      s!"    assert ¬ ({propText})\n  }\n"
    if expected then logInfo msg else logError msg
    if doCertify then
      let certificationStarted ← IO.monoMsNow
      let cert ← certifyUnsafe mod property path
      reportPhaseTime "certification" certificationStarted
      logInfo s!"Certified: theorem {cert.theoremName} refutes {propertyName} at the model's sort sizes and typeclass instances; axioms: {cert.axioms}; {certificateStatus cert}"
  | .unsafeUndecoded steps reason =>
    let certifyNote := if doCertify then "; no certificate is built" else ""
    logError s!"Violated: {propertyName}{trustedNote}. The solver found an execution of {steps} step(s) that breaks it, but its model could not be decoded ({reason.take 300}), so the execution is not shown{certifyNote}."
  | .noUniversalInvariant diagrams check =>
    -- Ghost definitions are not symbols of the vocabulary: a clause over one
    -- unfolds to its body, and a body with a quantifier is not universal.
    let ghosts := Signature.ghostDefinitions mod
    let ghostNote := if ghosts.isEmpty then "" else
      s!"The ghost definitions {", ".intercalate (ghosts.map toString).toList} are outside that vocabulary: a clause over one of them unfolds to its body, and when the body has a quantifier the clause is not universal, so this verdict says nothing about such clauses. "
    -- Class fields whose result type is outside the sorts are not symbols
    -- of the vocabulary either.
    let excluded := sig.excludedClassFields
    let excludedNote := if excluded.isEmpty then "" else
      s!"The class fields {", ".intercalate (excluded.map toString).toList} are outside that vocabulary (their result type is outside the module's sorts), so this verdict says nothing about clauses over them. "
    -- The paper states Proposition 5.6 for constants and relations; the
    -- message says when the verdict rests on the extension of it made here.
    let basis := if sig.extendsPaper
      then "Proposition 5.6 of the paper, extended here to function symbols and enum sorts; see docs/Invariant-Synthesis.md"
      else "Proposition 5.6 of the paper"
    let mut msg := s!"No universal inductive invariant over the module's vocabulary proves {propertyName}{trustedNote}. {ghostNote}{excludedNote}" ++
      s!"Abstract counterexample, {diagrams.size} structure(s): {chainDescription} ({basis}).\n"
    for i in [:diagrams.size] do
      msg := msg ++ s!"  structure {i + 1}:\n{renderState diagrams[i]!}\n"
    -- The verdict stands whatever the bounded check said, but without an
    -- answer from it the property may be false as well.
    if let .noAnswer k r := check then
      msg := msg ++ s!"The bounded path check of {k} step(s) got no answer ({r.take 160}), so an execution of that length may violate the property.\n"
    if expected then logInfo msg else logWarning msg
  | .absenceWithheld diagrams check frameSizes =>
    -- The chain would be the absence verdict for a vocabulary without
    -- integers; here it is shown and no verdict is given.
    let checkNote := match check with
      | .notAsked => "The chain starts above the initial frame, so it describes no execution of the frames' length. "
      | .noPath k => s!"No execution of {k} step(s) violates the property, so the chain is not a real execution of that length. "
      | .noAnswer k r => s!"The bounded path check of {k} step(s) got no answer ({r.take 160}), so a real execution of that length may exist. "
    let mut msg := s!"IC3 stopped: the search closed without an invariant. The no-universal-invariant verdict is not given for a module with integer state (Proposition 5.6 of the paper is about uninterpreted sorts), so this is not a verdict. {frameSummary frameSizes}. " ++
      s!"Abstract counterexample, {diagrams.size} structure(s): {chainDescription}.\n"
    for i in [:diagrams.size] do
      msg := msg ++ s!"  structure {i + 1}:\n{renderState diagrams[i]!}\n"
    msg := msg ++ checkNote ++
      "The property may need a strengthening outside the universal fragment (a Skolem ghost function makes an existential fact universal; see \"Existential invariants\" in docs/Invariant-Synthesis.md), or it is false by a longer execution. Modeling the integer state as an ordered sort makes the no-universal-invariant verdict available for the remodeled module."
    if expected then logInfo msg else logWarning msg
  | .unknown reason frameSizes =>
    -- The hint follows the reason's text; every reason `SearchM.stop` is given
    -- embeds one of the markers below or a query answer that does.
    let has (marker : String) : Bool := (reason.splitOn marker).length > 1
    let hint :=
      if has "fuel exhausted" then
        "Raise the budget with `(fuel := n)`. When the frontier frame keeps growing without clearing (see the clause counts), the search is not converging and more budget will not help; `(generalizer := updr)` or `(cores := false)` change which clauses are tried."
      else if reason.startsWith "frame limit" then
        "The frame limit is a constant of `Config`; a search that reaches it is unlikely to converge, and the property may need an invariant outside the universal fragment."
      else if has "heartbeats" || has "exceeded its budget" then
        "The query overran the per-query heartbeat budget (a constant of `Query.lean`), most often in Veil's preprocessing of a large frame."
      else if has "failed:" then
        "A query could not be posed or its answer could not be read; this is a pipeline limitation, not a solver budget."
      else if has solverUnknownPrefix then
        "The query was asked twice, the second time with twice `veil.smt.timeout`; raise that option. Some modules produce queries outside the fragment cvc5 decides, and those run to the timeout however large."
      else ""
    let msg := s!"IC3 stopped: {reason}. {frameSummary frameSizes}.{if hint.isEmpty then "" else " " ++ hint}"
    if expected then logInfo msg else logWarning msg
  | .internalError message frameSizes =>
    logError s!"IC3 internal error: {message}. {frameSummary frameSizes}. This is a bug in the controller or in the model decoder, not a solver limit."

end Veil.Synthesizer
