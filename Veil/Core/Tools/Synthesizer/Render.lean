module

public meta import Lean
public meta import Veil.Core.Tools.Synthesizer.Clause

/-!
# Rendering clauses as Veil terms

A `Clause` becomes a Lean `Term` in the surface language a Veil module user
writes: `∀ (x0 x1 : node), ¬ leader x0 ∨ tot.le x1 x0`. State relations are
applied directly (Veil coerces the `Bool` field to `Prop`); typeclass fields
are written through the instance binder (`tot.le`), which is in scope both in
a Veil module body and in the query binders `Query.lean` builds. A function
symbol renders as the equation `curEpoch x0 = x1`, a sort-valued individual
or class constant as `now = x0`, and an enum constructor by its name
(`role x0 = leader`), which Veil brings into scope by opening the enum's
class when the enum is declared, or through the class
(`roleT_EnumClass.leader`) when the module declares the same name
(`Signature.enumConstructors`). The same rendering therefore serves the
solver queries and the clauses printed for the user to paste into the module.
-/

public meta section

namespace Veil.Synthesizer
open Lean Lean.Parser.Term

/-- Variable name for the `i`-th bound variable. -/
def varIdent (i : Nat) : Ident := mkIdent (Name.mkSimple s!"x{i}")

/-- The head of an atom as an identifier: the component name, or `inst.field`. -/
def RelSym.headTerm (r : RelSym) : Term := mkIdent r.key

def Arg.toTerm : Arg → Term
  | .var v => varIdent v
  | .enumConst ctor _ => mkIdent ctor

def NumTerm.toTerm [Monad m] [MonadQuotation m] (t : NumTerm) : m Term := do
  let head : Term := t.sym.headTerm
  let argTerms : Array Term := t.args.map Arg.toTerm
  if argTerms.isEmpty then pure head else `(term| $head $argTerms*)

/-- A numeral of a numeric sort, `(3 : Int)`. -/
def numeralTerm [Monad m] [MonadQuotation m] (sort : SortName) (n : Int) : m Term := do
  let lit : Term := Syntax.mkNumLit (toString n.natAbs)
  if n < 0 then `(term| (-$lit : $(mkIdent sort))) else `(term| ($lit : $(mkIdent sort)))

/-- The two sides of a linear constraint, negative coefficients moved to the
right so no subtraction is written: `x0 + 1 ≤ x1`, `a + b = c`. Each side is
a sum of `k * t` (or `t` when `k = 1`) and possibly a numeral; an empty side is
the numeral `0`. -/
def linSides [Monad m] [MonadQuotation m] (terms : Array (Int × NumTerm)) (c : Int) : m (Term × Term) := do
  let sort := (terms[0]?.map (·.2.sort)).getD `Int
  let side (ts : Array (Int × NumTerm)) (k : Int) : m Term := do
    let mut parts : Array Term := #[]
    for (coef, t) in ts do
      let tt ← t.toTerm
      parts := parts.push (← if coef == 1 then pure tt else `(term| $(Syntax.mkNumLit (toString coef.natAbs)) * $tt))
    if k > 0 then parts := parts.push (← numeralTerm sort k)
    if parts.isEmpty then numeralTerm sort 0 else
      parts[1:].foldlM (init := parts[0]!) fun acc p => `(term| $acc + $p)
  let lhs ← side (terms.filter (·.1 > 0)) c
  let rhs ← side ((terms.filter (·.1 < 0)).map fun (k, t) => (-k, t)) (-c)
  return (lhs, rhs)

def Atom.toTerm [Monad m] [MonadQuotation m] : Atom → m Term
  | .lin terms c isEq => do
    let (lhs, rhs) ← linSides terms c
    if isEq then `(term| $lhs = $rhs) else `(term| $lhs ≤ $rhs)
  | .rel sym args => do
    let head : Term := sym.headTerm
    let argTerms : Array Term := args.map Arg.toTerm
    if sym.isFunction && !argTerms.isEmpty then
      -- The graph atom `f a₁ … aₙ = b`; `b` is the last argument.
      let fnArgs := argTerms.pop
      let result := argTerms.back!
      let app : Term ← if fnArgs.isEmpty then pure head else `(term| $head $fnArgs*)
      `(term| $app = $result)
    else if argTerms.isEmpty then pure head else `(term| $head $argTerms*)
  | .eq a b => `(term| $(varIdent a) = $(varIdent b))

def Literal.toTerm [Monad m] [MonadQuotation m] (l : Literal) : m Term := do
  let t ← l.atom.toTerm
  if l.positive then pure t else `(term| ¬ $t)

/-- `∀ (x0 : s0) (x1 : s1), l0 ∨ l1 ∨ …`; an empty disjunction renders as `False`. -/
def Clause.toTerm [Monad m] [MonadQuotation m] (c : Clause) : m Term := do
  let lits ← c.lits.mapM Literal.toTerm
  let body : Term ← if lits.isEmpty then `(term| False) else
    lits[1:].foldlM (init := lits[0]!) fun acc l => `(term| $acc ∨ $l)
  if c.vars.isEmpty then return body
  let binders ← (Array.range c.vars.size).mapM fun i =>
    `(bracketedBinder| ($(varIdent i) : $(mkIdent c.vars[i]!)))
  `(term| ∀ $binders*, $body)

def Arg.toString : Arg → String
  | .var v => s!"x{v}"
  | .enumConst ctor _ => ctor.toString

/-- Pretty form for messages and for pasting into a module. -/
def Clause.toString (c : Clause) : String :=
  let lit (l : Literal) : String :=
    let a := match l.atom with
      | .rel sym args =>
        let head := sym.key.toString
        let strs := args.map Arg.toString
        if sym.isFunction && !strs.isEmpty then
          let app := if strs.size == 1 then head else head ++ " " ++ " ".intercalate strs.pop.toList
          s!"{app} = {strs.back!}"
        else if strs.isEmpty then head else head ++ " " ++ " ".intercalate strs.toList
      | .eq a b => s!"x{a} = x{b}"
      | .lin terms k0 isEq =>
        let term (t : NumTerm) : String :=
          let strs := t.args.map Arg.toString
          if strs.isEmpty then t.sym.key.toString else t.sym.key.toString ++ " " ++ " ".intercalate strs.toList
        let side (ts : Array (Int × NumTerm)) (k : Int) : String :=
          let parts := ts.map fun (coef, t) => if coef == 1 then term t else s!"{coef.natAbs} * {term t}"
          let parts := if k > 0 then parts.push (ToString.toString k) else parts
          if parts.isEmpty then "0" else " + ".intercalate parts.toList
        s!"{side (terms.filter (·.1 > 0)) k0} {if isEq then "=" else "≤"} {side ((terms.filter (·.1 < 0)).map fun (k, t) => (-k, t)) (-k0)}"
    if l.positive then a else s!"¬ {a}"
  let body := if c.lits.isEmpty then "False" else " ∨ ".intercalate (c.lits.map lit).toList
  if c.vars.isEmpty then body else
    let binders := " ".intercalate ((Array.range c.vars.size).map fun i => s!"(x{i} : {c.vars[i]!})").toList
    s!"∀ {binders}, {body}"

instance : ToString Clause := ⟨Clause.toString⟩

end Veil.Synthesizer
