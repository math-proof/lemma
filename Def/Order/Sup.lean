import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Set.Image
import Syntax.Order.Sup


open Lean in
/-- Parse a `supBinder`: `(x : T)`, `x : T`, or bare `x`.
The syntax category wraps each alternative in a `group` node, so we match on raw args. -/
def parseSupBinder (stx : TSyntax `supBinder) : MacroM (TSyntax `ident × Option (TSyntax `term)) := do
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
/-- Right-nested product type `T₀ × (T₁ × (⋯ × Tₙ))`, with `_` for untyped slots. -/
def mkProdTy (tys : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  let mut tyProd := tys[tys.size - 1]!
  for i in (List.range (tys.size - 1)).reverse do
    tyProd ← `($(tys[i]!) × $tyProd)
  pure tyProd

open Lean in
/-- Projection `x.2.2.1` for binder index `i` of `n` in a right-nested product. -/
def mkSupProj (x : TSyntax `ident) (n i : Nat) : MacroM (TSyntax `term) := do
  let mut p : TSyntax `term := ⟨x.raw⟩
  if i = n - 1 then
    for _ in List.range i do
      p ← `($p.2)
    pure p
  else
    for _ in List.range i do
      p ← `($p.2)
    `($p.1)

open Lean in
/-- `fun` over binders: single binder stays a plain `fun x` / `fun (x : T)`;
multiple binders use one packed variable with product type + `let` projections
(avoids match-pattern metavariable errors on bare slots). -/
def mkRangeFun (binders : Array (TSyntax `ident × Option (TSyntax `term)))
    (e : TSyntax `term) : MacroM (TSyntax `term) := do
  if h : binders.size = 1 then
    let (x, ty?) := binders[0]
    match ty? with
    | some ty => `(fun ($x:ident : $ty) ↦ $e)
    | none => `(fun $x:ident ↦ $e)
  else
    let tys ← binders.mapM fun
      | (_, some ty) => pure ty
      | (_, none) => `(_)
    let tyProd ← mkProdTy tys
    -- Hygienic pack binder (Macro.addMacroScope): bare mkIdent `x shadows user binder x.
    let x : TSyntax `ident := mkIdent (← Macro.addMacroScope `_supPack)
    let n := binders.size
    let mut body := e
    -- bind from last to first; body uses binder names via lets
    for i in (List.range n).reverse do
      let (name, _) := binders[i]!
      let proj ← mkSupProj x n i
      body ← `(let $name:ident := $proj; $body)
    `(fun ($x:ident : $tyProd) ↦ $body)

