import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Image


/--
[sympy.Sup](https://github.com/sympy/sympy) with a finiteness bound, as written in the sympy
proofs: `Sup[s[t].bvar, t](Abs(f)) < oo`.

`sup[x, y] e < ∞` says that the real-valued function `(x, y) ↦ e` is bounded above, i.e.
`sup e < ∞`; write `sup[x] ‖f x‖ < ∞` or `sup[x] |f x| < ∞` to say that `f` is absolutely bounded. It elaborates to
`BddAbove (Set.range fun (x, y) ↦ e)` (a single binder gives `BddAbove (Set.range fun x ↦ e)`).

Binders may be bare `ident`, typed `ident : type` (Python-style, preferred), or typed
`(ident : type)`. Guillemet names work in all forms:
`sup[θ, t, «s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A] e < ∞`
(typed slots ascribe types; bare slots stay `_` and are inferred from `e`).

The body is parsed at precedence 51, just above `<`, so `sup[x] ‖f x‖ + 1 < ∞` bounds the sum
`‖f x‖ + 1`, and `‖f x‖`, `|f x|` and applications need no parentheses.

The optional filter `sup[x, y | c] e < ∞` restricts the supremum to the points satisfying `c`;
it is `BddAbove ((fun (x, y) ↦ e) '' {(x, y) | c})`.
-/
syntax
  supBinder := ("(" ident " : " term ")") <|> (ident (" : " term)?)

syntax:50 (name :=
  supLtTop) "sup[" sepBy1(supBinder, ", ") "] " term:51 " < " "∞" : term

/-- `sup[x, y | c] e < ∞`: `e` is bounded above on the points `(x, y)` satisfying `c`. -/
syntax:50 (name :=
 supLtTopFilter) "sup[" sepBy1(supBinder, ", ") " | " term "] " term:51 " < " "∞" : term

