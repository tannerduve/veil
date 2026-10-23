module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `DieHard.lean` with `not_solved` stated as `safety`: the property is false,
and `#synthesize_invariants` finds an execution that leaves 4 litres in the
big jug and certifies it as `DieHardSynthesis.ic3_unsafe`. -/



veil module DieHardSynthesis

individual big : Nat
individual small : Nat

#gen_state

after_init {
  big := 0
  small := 0
}


action FillSmallJug {
  small := 3
  big := big
}


action FillBigJug  {
  big := 5
  small := small
}


action EmptySmallJug {
  small := 0
  big := big
}


action EmptyBigJug {
  big := 0
  small := small
}


action SmallToBig {
  let tmp := big
  big := if big + small < 5 then big + small else 5
  small := small - (big - tmp)
}



action BigToSmall {
  let tmp := small
  small := if big + small < 3 then big + small else 3
  big := big - (small - tmp)
}


safety [not_solved] big ≠ 4
#gen_spec

#synthesize_invariants (expect := unsafe) certify

end DieHardSynthesis
