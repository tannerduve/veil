module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `DecentralizedLock.lean` without its hand-written invariants: `mutex` is
inductive on its own, and `#synthesize_invariants` certifies it as
`DecentralizedLockSynthesis.ic3_safe`. -/


-- https://github.com/aman-goel/ivybench/blob/master/ex/ivy/decentralized-lock.ivy


veil module DecentralizedLockSynthesis

type node
type time

immutable relation le : time -> time -> Bool
relation has_lock : node -> Bool
relation msg : node -> time -> Bool
function epoch : node -> time

immutable individual first : node
immutable individual zero : time
immutable individual max : time

#gen_state

assumption ∀ (x: time), le x X
assumption ∀ (x y z : time), le x y ∧ le y z → le x z
assumption ∀ (x y : time), le x y ∧ le y x → x = y
assumption ∀ (x y : time), le x y ∨ le y x
assumption ∀ (x : time), le zero x
assumption ∀ (x : time), le x max

after_init {
  has_lock X := decide $ X = first;
  msg Y T := false;
  epoch X := zero
}

action take_lock (x : node) (y : node) (t : time) {
    require msg y t;
    require ¬ le t (epoch y);
    has_lock y := true;
    epoch y := t
}

action release_lock (x : node) (y : node) (t : time) {
    require has_lock x;
    require ¬ le t (epoch x);
    has_lock x := false;
    msg y t := true
}

safety [mutex] ¬ (has_lock X ∧ has_lock Y ∧ X ≠ Y)

#gen_spec

#synthesize_invariants (expect := invariant) certify

end DecentralizedLockSynthesis
