module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `Traffic.lean` with `puzzle_unsolvable` stated as `safety`: the property is
false, and `#synthesize_invariants` finds an execution that solves the
puzzle and certifies it as `TrafficSynthesis.ic3_unsafe`. -/


veil module TrafficSynthesis
-------------------------------- MODULE traffic ------------------------------

-- src: https://github.com/Apress/practical-tla-plus/blob/master/Chapter%206/traffic.tla

enum Color = {red, green}

enum ProcSet = {light, car}
enum states = {Cycle, Drive, Done}
individual at_light : Bool
individual LIGHT : Color
relation pc (P : ProcSet) (S : states)

#gen_state

-- Init == (* Global variables *)
--         /\ at_light = TRUE
--         /\ light = "red"
--         /\ pc = [self \in ProcSet |-> CASE self = "light" -> "Cycle"
--                                         [] self = "car" -> "Drive"]
after_init {
  at_light := true
  LIGHT := red
  pc P S := if P == light then S == Cycle else S == Drive
}

-- Cycle == /\ pc["light"] = "Cycle"
--          /\ IF at_light
--                THEN /\ light' = NextColor(light)
--                     /\ pc' = [pc EXCEPT !["light"] = "Cycle"]
--                ELSE /\ pc' = [pc EXCEPT !["light"] = "Done"]
--                     /\ light' = light
--          /\ UNCHANGED at_light
action Cycle {
  require pc light Cycle
  if at_light then
    -- NextColor: red -> green, green -> red
    LIGHT := if LIGHT == red then green else red
    pc light S := S == Cycle
  else
    pc light S := S == Done
}

-- Drive == /\ pc["car"] = "Drive"
--          /\ light = "green"
--          /\ at_light' = FALSE
--          /\ pc' = [pc EXCEPT !["car"] = "Done"]
--          /\ light' = light
action Drive {
  require pc car Drive
  require LIGHT == green
  at_light := false
  pc car S := S == Done
}

/- Corresponding to Line 67:
`Termination == <>(\A self \in ProcSet: pc[self] = "Done")`
in Traffic.tla. The explaination has been given in `MutexViolation.lean`,
which is the same as `action Terminating` there. -/
action shutter_termination {
  require (∀p, pc p Done)
}

safety [puzzle_unsolvable]
  -- Car is always at the light (negated goal)
  at_light = true

#gen_spec

#synthesize_invariants (expect := unsafe) certify

end TrafficSynthesis
