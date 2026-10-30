import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max


/--
Value-level maximum over a finite nonempty index type, written like the py
`Maxima[b](f(b))` / `ReducedMax(f)`:

* `max[b] e` is `Finset.univ.sup' Finset.univ_nonempty (fun b => e)` (needs `[Fintype _] [Nonempty _]`),
* `max[b : T] e` / `max[b:T] e` give a type per binder (also covers the old shared-type spelling
  when there is a single binder),
* `max[(b : T)] e` / `max[a, (b : T)] e` still accept parenthesized typed binders,
* `max[a : A, b : B] e` types each binder independently,
* `max[a, b] e` is `max[a] max[b] e`.

The body is parsed at precedence 67 (like `∑`), so `max[ys : Fin n → Y] P ys` needs no
parentheses while `max[b] (f b + g b)` does.  It never clashes with `sup[x] e < ∞`
(see `Syntax/Order/Sup.lean`), which uses a different head token.

Note: `max[a, b : T]` parses as an untyped `a` and a typed `b : T` (not a shared type on
both). Prefer `max[a : T, b : T]` when every binder should have type `T`. The trailing
shared-type form `max[a, b : T]` of older revisions is therefore superseded for ≥2 binders.
-/
syntax maxBinder := ("(" ident " : " term ")") <|> (ident (" : " term)?)

syntax:67 (name := maxVal) "max[" sepBy1(maxBinder, ", ") (" : " term)? "] " term:67 : term

open Lean in
/-- Parse a `maxBinder`: `(x : T)`, `x : T`, or bare `x`.
The syntax category wraps each alternative in a `group` node, so we match on raw args. -/
def parseMaxBinder (stx : TSyntax `maxBinder) : MacroM (TSyntax `ident × Option (TSyntax `term)) := do
  let g := stx.raw[0]
  let args := g.getArgs
  if args.size == 5 then
    pure (⟨args[1]!⟩, some ⟨args[3]!⟩)
  else if args.size == 2 then
    let x : TSyntax `ident := ⟨args[0]!⟩
    let opt := args[1]!
    if opt.getArgs.isEmpty then
      pure (x, none)
    else
      pure (x, some ⟨opt[1]!⟩)
  else
    Macro.throwErrorAt stx "expected binder `x`, `x : T`, or `(x : T)`"

open Lean in
macro_rules
  | `(max[$xs:maxBinder,*] $e) => do
    let binders ← xs.getElems.mapM parseMaxBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      r ← match ty? with
        | some ty => `(Finset.univ.sup' Finset.univ_nonempty (fun ($x:ident : $ty) => $r))
        | none => `(Finset.univ.sup' Finset.univ_nonempty (fun $x:ident => $r))
    pure r
  | `(max[$xs:maxBinder,* : $T] $e) => do
    let binders ← xs.getElems.mapM parseMaxBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      let ty := ty?.getD T
      r ← `(Finset.univ.sup' Finset.univ_nonempty (fun ($x:ident : $ty) => $r))
    pure r
