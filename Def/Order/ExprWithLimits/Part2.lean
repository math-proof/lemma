import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Syntax.Order.ExprWithLimits


open Lean in
def parseArgExtBinder (stx : TSyntax `argExtBinder) :
    MacroM (TSyntax `ident × Option (TSyntax `term)) := do
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

