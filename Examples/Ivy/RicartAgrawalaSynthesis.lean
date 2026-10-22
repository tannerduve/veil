module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `RicartAgrawala.lean` without its two hand-written invariants:
`#synthesize_invariants` finds an inductive strengthening of
`mutual_exclusion` and certifies it as `RicartAgrawalaSynthesis.ic3_safe`. -/


-- https://github.com/aman-goel/ivybench/blob/d2c9298fdd099001c71a34bc2e118db6f07d8404/distai/ivy/Ricart-Agrawala.ivy


veil module RicartAgrawalaSynthesis

type node

relation requested (n1 : node) (n2 : node)
relation replied (n1 : node) (n2 : node)
relation holds (n : node)

#gen_state

after_init {
  requested N1 N2 := false;
  replied N1 N2 := false;
  holds N := false
}

action request (requester: node) (responder : node) {
  require ¬ requested requester responder;
  require requester ≠ responder;
  requested requester responder := true
}

action reply (requester: node) (responder: node) {
    require ¬ replied requester responder;
    require ¬ holds responder;
    require ¬ replied responder requester;
    require requested requester responder;
    require requester ≠ responder;
    requested requester responder := false;
    replied requester responder := true
}

action enter (requester: node) {
  require ∀ N, (N ≠ requester) → replied requester N;
  holds requester := true
}

action leave (requester : node) {
  require holds requester;
  holds requester := false;
  replied requester N := false
}

safety [mutual_exclusion] (holds N1 ∧ holds N2) → N1 = N2

#gen_spec

#synthesize_invariants (expect := invariant) certify

end RicartAgrawalaSynthesis
