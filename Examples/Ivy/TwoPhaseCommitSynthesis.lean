module

public import Veil
public import Veil.Core.Tools.Synthesizer

/-! `TwoPhaseCommit.lean` without its hand-written invariants:
`#synthesize_invariants` finds an inductive strengthening of its safety
property and certifies it as `TwoPhaseCommitSynthesis.ic3_safe`. -/


-- https://github.com/aman-goel/ivybench/blob/master/i4/ivy/two_phase_commit.ivy

veil module TwoPhaseCommitSynthesis


type node

relation vote_yes : node -> Bool
relation vote_no : node -> Bool
relation alive : node -> Bool
relation go_commit : node -> Bool
relation go_abort : node -> Bool
relation decide_commit : node -> Bool
relation decide_abort : node -> Bool

individual abort_flag : Bool

#gen_state

after_init {
  vote_yes N := false;
  vote_no N := false;
  alive N := true;
  go_commit N := false;
  go_abort N := false;
  decide_commit N := false;
  decide_abort N := false;
  abort_flag := false
}

action vote1 (n : node) {
  require alive n;
  require ¬vote_no n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_yes n := true
}

action vote2(n: node) {
  require alive n;
  require ¬vote_yes n;
  require ¬decide_commit n;
  require ¬decide_abort n;
  vote_no n := true;
  abort_flag := true;
  decide_abort n := true
}

action fail(n: node) {
  require alive n;
  alive n := false;
  abort_flag := true
}

action go1 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require ∀ N, vote_yes N;
  go_commit N := true
}

action go2 {
  require ∀ N, ¬go_commit N;
  require ∀ N, ¬go_abort N;
  require exists n, vote_no n ∨ ¬alive n;
  go_abort N := true
}

action commit(n: node) {
  require alive n;
  require go_commit n;
  decide_commit n := true
}

action abort(n: node) {
  require alive n;
  require go_abort n;
  decide_abort n := true
}

safety (decide_commit N → ¬decide_abort N2)
      ∧ (decide_commit N -> vote_yes N2)
      ∧ (decide_abort N → abort_flag)
#gen_spec

#synthesize_invariants (expect := invariant) certify

end TwoPhaseCommitSynthesis
