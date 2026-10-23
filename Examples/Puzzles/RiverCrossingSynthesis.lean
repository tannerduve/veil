module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `RiverCrossing.lean` with `unsolved` stated as `safety`: the property is
false, and `#synthesize_invariants` finds an execution that solves the puzzle
and certifies it as `RiverCrossingSynthesis.ic3_unsafe`. -/


veil module RiverCrossingSynthesis

enum position = {near, far}
individual wolf_pos : position
individual goat_pos : position
individual cabbage_pos : position
individual farmer_pos : position

-- enum act = {Init, FarmerAndWolf, FarmerAndGoat, FarmerAndCabbage, FarmerAlone}
-- individual lastAction : act

#gen_state

/-
Puzzle Rules:
 * If goat and wolf are on the same bank p, the farmer must also be on p.
 * If goat and cabbage are on the same bank p, the farmer must also be on p.
-/
ghost relation safety_constraint :=
     (goat_pos = wolf_pos → farmer_pos = goat_pos) ∧
     (goat_pos = cabbage_pos → farmer_pos = goat_pos)

after_init {
  wolf_pos := near
  goat_pos := near
  cabbage_pos := near
  farmer_pos := near
}

action FarmerAndWolf {
  require farmer_pos = wolf_pos
  if farmer_pos = far then
    farmer_pos := near
    wolf_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    wolf_pos := far
    assume safety_constraint
}

action FarmerAndGoat {
  require farmer_pos = goat_pos
  if farmer_pos = far then
    farmer_pos := near
    goat_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    goat_pos := far
    assume safety_constraint
}


action FarmerAndCabbage {
  require farmer_pos = cabbage_pos
  if farmer_pos = far then
    farmer_pos := near
    cabbage_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    cabbage_pos := far
    assume safety_constraint
}

action FarmerAlone {
  if farmer_pos = far then
    farmer_pos := near
    assume safety_constraint
  else
    farmer_pos := far
    assume safety_constraint
}

safety [unsolved] ¬ (goat_pos = far ∧ wolf_pos = far ∧ cabbage_pos = far ∧ farmer_pos = far)

#gen_spec

#synthesize_invariants (expect := unsafe) certify

end RiverCrossingSynthesis
