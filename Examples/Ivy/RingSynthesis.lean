module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `Ring.lean` without its hand-written invariants: `#synthesize_invariants`
finds an inductive strengthening of `single_leader` and certifies it as
`RingSynthesis.ic3_safe`. -/


veil module RingSynthesis

type node
instantiate tot : TotalOrder node
instantiate btwn : Between node

open Between TotalOrder

relation leader : node → Bool
relation pending : node → node → Bool

#gen_state

after_init {
  leader N := false
  pending M N := false
}

ghost relation isNext (n : node) (next : node) :=
  ∀ Z, n ≠ next ∧ ((Z ≠ n ∧ Z ≠ next) → btw n next Z)

action send (n next : node) {
  require isNext n next
  pending n next := true
}

action recv (sender n next : node) {
  require isNext n next
  require pending sender n
  pending sender n := false
  if (sender = n) then
    leader n := true
  else
    if (le n sender) then
      pending sender next := true
}

safety [single_leader] leader N ∧ leader M → N = M
set_option veil.smt.trust false
#gen_spec

#synthesize_invariants (expect := invariant) certify

end RingSynthesis
