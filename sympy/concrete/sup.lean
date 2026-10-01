import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Image

/--
[sympy.Sup](https://github.com/sympy/sympy) with a finiteness bound, as written in the sympy
proofs: `Sup[s[t].bvar, t](Abs(f)) < oo`.

`sup[x, y] e < ∞` says that the real-valued function `(x, y) ↦ e` is bounded above, i.e.
`sup e < ∞`; write `sup[x] ‖f x‖ < ∞` or `sup[x] |f x| < ∞` to say that `f` is absolutely bounded. It elaborates to
`BddAbove (Set.range fun (x, y) ↦ e)` (a single binder gives `BddAbove (Set.range fun x ↦ e)`).

The body is parsed at precedence 51, just above `<`, so `sup[x] ‖f x‖ + 1 < ∞` bounds the sum
`‖f x‖ + 1`, and `‖f x‖`, `|f x|` and applications need no parentheses.

The optional filter `sup[x, y | c] e < ∞` restricts the supremum to the points satisfying `c`;
it is `BddAbove ((fun (x, y) ↦ e) '' {(x, y) | c})`.
-/
syntax:50 (name := supLtTop) "sup[" ident,+ "] " term:51 " < " "∞" : term

/-- `sup[x, y | c] e < ∞`: `e` is bounded above on the points `(x, y)` satisfying `c`. -/
syntax:50 (name := supLtTopFilter) "sup[" ident,+ " | " term "] " term:51 " < " "∞" : term

open Lean in
private def mkTuplePat (xs : Array (TSyntax `ident)) : MacroM (TSyntax `term) :=
  if h : xs.size = 1 then pure ⟨xs[0].raw⟩
  else do
    let ts : Array (TSyntax `term) := xs.map fun x => ⟨x.raw⟩
    `(($(ts[0]!), $(ts[1:]),*))

macro_rules
  | `(sup[$xs:ident,*] $e < ∞) => do
    let xs := xs.getElems
    let pat ← mkTuplePat xs
    `(BddAbove (Set.range fun $pat ↦ $e))
  | `(sup[$xs:ident,* | $c] $e < ∞) => do
    let xs := xs.getElems
    let pat ← mkTuplePat xs
    `(BddAbove ((fun $pat ↦ $e) '' {p | match p with | $pat => $c}))
