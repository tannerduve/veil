module

public import Veil.Core.Tools.ModelChecker.TransitionSystem

/-!
# Soundness of a UPDR certificate

What the controller produces at a fixpoint is a set of clauses `c₁ … cₖ`
together with solver verdicts. What a user needs is a theorem about the
module's relational transition system: every reachable state satisfies the
property. This file proves, once and for all, that the two solver-checked
conditions (initiation: the invariant holds in every initial state;
consecution: every transition preserves it) imply that theorem. The
per-module proof terms that discharge the
two conditions are assembled by `Certificate.lean`; this file is the only
place where induction on reachability happens.

Nothing here depends on a particular module or on the controller. It is a
statement about `Veil.RelationalTransitionSystem`.
-/

@[expose] public section

namespace Veil.Synthesizer
open Veil

variable {ρ σ l : Type}

/-- The inductive-invariant principle: if `Inv` holds initially and is
preserved by every transition (under the theory assumptions), then `Inv`
holds in every reachable state. -/
theorem reachable_of_inductive (sys : RelationalTransitionSystem ρ σ l) (Inv : ρ → σ → Prop)
    (hinit : ∀ th s, sys.assumptions th → sys.init th s → Inv th s)
    (hcons : ∀ th s lbl s', sys.assumptions th → Inv th s → sys.tr th s lbl s' → Inv th s') :
    ∀ th s, sys.reachable th s → Inv th s := by
  intro th s h
  induction h with
  | init s has hinit' => exact hinit th s has hinit'
  | step s s' hr hn ih =>
    obtain ⟨lbl, htr⟩ := hn
    exact hcons th s lbl s' (sys.reachable_assumptions th s hr) ih htr

/-- Soundness of a certificate: an inductive `Inv` that implies `P` proves `P`
of every reachable state. `Inv` is `P ∧ c₁ ∧ … ∧ cₖ`, so `himp` is trivial in
practice; it is kept explicit so the statement does not fix the shape of `Inv`. -/
theorem property_of_certificate (sys : RelationalTransitionSystem ρ σ l) (Inv P : ρ → σ → Prop)
    (hinit : ∀ th s, sys.assumptions th → sys.init th s → Inv th s)
    (hcons : ∀ th s lbl s', sys.assumptions th → Inv th s → sys.tr th s lbl s' → Inv th s')
    (himp : ∀ th s, Inv th s → P th s) :
    ∀ th s, sys.reachable th s → P th s :=
  fun th s h => himp th s (reachable_of_inductive sys Inv hinit hcons th s h)

/-! ## Certifying counterexamples

A counterexample is a path: an initial state followed by labeled steps.
`pathValid` says every step is a transition; `pathLast` is the state the path
ends in. Both are structural recursions on the step list, so the proof that
the last state is reachable is a plain induction. -/

/-- Every step of the path is a transition of `sys` under theory `th`. -/
def pathValid (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : σ → List (l × σ) → Prop
  | _, [] => True
  | s, (lbl, s') :: rest => sys.tr th s lbl s' ∧ pathValid sys th s' rest

/-- The last state of a path starting at `s`. -/
def pathLast : σ → List (l × σ) → σ
  | s, [] => s
  | _, (_, s') :: rest => pathLast s' rest

theorem reachable_of_pathValid (sys : RelationalTransitionSystem ρ σ l) (th : ρ) :
    ∀ (s : σ) (steps : List (l × σ)), sys.reachable th s → pathValid sys th s steps →
      sys.reachable th (pathLast s steps) := by
  intro s steps
  induction steps generalizing s with
  | nil => intro h _; exact h
  | cons step rest ih =>
    obtain ⟨lbl, s'⟩ := step
    intro hr ⟨htr, hrest⟩
    exact ih s' (.step s s' hr ⟨lbl, htr⟩) hrest

/-- A path from an initial state to a state violating `P` refutes the safety
claim: `P` does not hold of every reachable state. -/
theorem unsafe_of_path (sys : RelationalTransitionSystem ρ σ l) (P : ρ → σ → Prop) (th : ρ) (s₀ : σ)
    (steps : List (l × σ)) (has : sys.assumptions th) (hinit : sys.init th s₀)
    (hvalid : pathValid sys th s₀ steps) (hbad : ¬ P th (pathLast s₀ steps)) :
    ¬ (∀ th s, sys.reachable th s → P th s) := fun hsafe =>
  hbad (hsafe th _ (reachable_of_pathValid sys th s₀ steps (.init s₀ has hinit) hvalid))

end Veil.Synthesizer
