module

public meta import Veil.Core.Tools.Synthesizer.Clause

/-! Laws of the clause layer of `#synthesize_invariants`, on a two-node Ring
state: evaluation of a structure's diagram and of its blocking clause,
subsumption up to variable renaming, and generalization by dropping literals
of the blocking clause. -/

meta section
open Veil.Synthesizer

def leaderSym : RelSym := { name := `leader, source := .state, argSorts := #[`node] }
def pendingSym : RelSym := { name := `pending, source := .state, argSorts := #[`node, `node] }
def leSym : RelSym := { name := `le, source := .typeclassField `tot `le, argSorts := #[`node, `node] }

/-- leader = {1}, pending = everything, le = {(0,0), (0,1), (1,1)}. -/
def st0 : FinStructure :=
  { sorts := #[(`node, 2)],
    rels := #[(leaderSym, #[#[1]]), (pendingSym, #[#[0,0], #[0,1], #[1,0], #[1,1]]),
              (leSym, #[#[0,0], #[0,1], #[1,1]])] }

/-- No leader and no messages: contains no copy of `st0`. -/
def stEmpty : FinStructure :=
  { sorts := #[(`node, 2)], rels := #[(leaderSym, #[]), (pendingSym, #[]), (leSym, #[#[0,0], #[0,1], #[1,1]])] }

/-- Three nodes, containing `st0` as the substructure on nodes {0, 1}. -/
def stBig : FinStructure :=
  { sorts := #[(`node, 3)],
    rels := #[(leaderSym, #[#[1]]), (pendingSym, #[#[0,0], #[0,1], #[1,0], #[1,1], #[2,2]]),
              (leSym, #[#[0,0], #[0,1], #[1,1], #[0,2], #[1,2], #[2,2]])] }

/-- One node, which is the leader: too small to contain `st0`. -/
def stOne : FinStructure :=
  { sorts := #[(`node, 1)], rels := #[(leaderSym, #[#[0]]), (pendingSym, #[]), (leSym, #[#[0,0]])] }

-- Evaluation: a structure satisfies its own diagram and violates its blocking
-- clause, which excludes exactly the structures containing a copy of it.
#guard st0.modelsExistential (st0.elements.map (·.1)) st0.diagramLiterals
#guard !st0.models st0.negatedDiagram
#guard !stBig.models st0.negatedDiagram
#guard stEmpty.models st0.negatedDiagram
#guard stOne.models st0.negatedDiagram

-- Subsumption up to renaming: `∀ x0 x1, ¬ leader x0 ∨ le x1 x0` subsumes
-- `∀ x0 x1, ¬ leader x1 ∨ ¬ pending x0 x1 ∨ le x0 x1` and not the reverse; a
-- non-injective renaming takes "no messages" to "no self-messages".
def leaderGreatest : Clause :=
  { vars := #[`node, `node],
    lits := #[{ positive := false, atom := .rel leaderSym #[0] }, { positive := true, atom := .rel leSym #[1, 0] }] }
def leaderGreatestWeak : Clause :=
  { vars := #[`node, `node],
    lits := #[{ positive := false, atom := .rel leaderSym #[1] }, { positive := false, atom := .rel pendingSym #[0, 1] },
              { positive := true, atom := .rel leSym #[0, 1] }] }
def noMessages : Clause := { vars := #[`node, `node], lits := #[{ positive := false, atom := .rel pendingSym #[0, 1] }] }
def noSelfMessages : Clause := { vars := #[`node], lits := #[{ positive := false, atom := .rel pendingSym #[0, 0] }] }
#guard leaderGreatest.subsumes leaderGreatestWeak && !leaderGreatestWeak.subsumes leaderGreatest
#guard noMessages.subsumes noSelfMessages && !noSelfMessages.subsumes noMessages
#guard Clause.removeSubsumed #[leaderGreatestWeak, noSelfMessages, leaderGreatest, noMessages] == #[leaderGreatest, noMessages]

-- Generalization: any literals dropped from the blocking clause leave a
-- clause that still excludes `st0`, subsumes the blocking clause, and
-- excludes more: keeping only `¬ leader x1` gives `∀ x0, ¬ leader x0`, which
-- also excludes the one-node state.
def keepOnly (c : Clause) (l : Literal) : Clause := ({ c with lits := c.lits.filter (· == l) } : Clause).pruneVars
def noLeader : Clause := keepOnly st0.negatedDiagram { positive := false, atom := .rel leaderSym #[1] }
#guard noLeader == { vars := #[`node], lits := #[{ positive := false, atom := .rel leaderSym #[0] }] }
#guard (List.range st0.negatedDiagram.numLits).all fun i => !st0.models (st0.negatedDiagram.deleteLiteral i)
#guard !st0.models noLeader && noLeader.subsumes st0.negatedDiagram
#guard !stOne.models noLeader

end
