import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

/--
Value-level maximum over a finite nonempty index type, written like the py
`Maxima[b](f(b))` / `ReducedMax(f)`:

* `max[b] e` is `Finset.univ.sup' Finset.univ_nonempty (fun b => e)` (needs `[Fintype _] [Nonempty _]`),
* `max[b : T] e` fixes the index type,
* `max[a, b] e` is `max[a] max[b] e`.

The body is parsed at precedence 67 (like `∑`), so `max[ys : Fin n → Y] P ys` needs no
parentheses while `max[b] (f b + g b)` does.  It never clashes with `sup[x] e < ∞`
(see `sympy/concrete/sup.lean`), which uses a different head token.
-/
syntax:67 (name := maxVal) "max[" ident,+ (" : " term)? "] " term:67 : term

open Lean in
macro_rules
  | `(max[$xs:ident,*] $e) => do
    let mut r : TSyntax `term := e
    for x in xs.getElems.reverse do
      r ← `(Finset.univ.sup' Finset.univ_nonempty (fun $x:ident => $r))
    pure r
  | `(max[$xs:ident,* : $T] $e) => do
    let mut r : TSyntax `term := e
    for x in xs.getElems.reverse do
      r ← `(Finset.univ.sup' Finset.univ_nonempty (fun ($x:ident : $T) => $r))
    pure r


-- created on 2026-10-02