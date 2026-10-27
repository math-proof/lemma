import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits.Part2
open Lean
open scoped Topology


partial def isZeroSyntax? : Syntax → Bool
  | `(0) => true
  | `(OfNat.ofNat $_ 0 $_) => true
  | stx =>
    match stx with
    | .atom _ val => val == "0"
    | _ => false

partial def archimedeanMkArg? : Syntax → Option Syntax
  | `(ArchimedeanClass.mk $x) => some x
  | `(@ArchimedeanClass.mk $_ $x) => some x
  | stx =>
    match stx with
    | .node _ `ArchimedeanClass.mk args =>
      if 0 < args.size then some args[args.size - 1]! else none
    | _ => none

@[app_unexpander LT.lt]
def tendsToLt.unexpand : PrettyPrinter.Unexpander
  | `($_ $a $b) =>
    if let some x := archimedeanMkArg? a then
      if isZeroSyntax? b then
        let x : TSyntax `term := ⟨x⟩
        `(($x → ∞))
      else
        throw ()
    else if isZeroSyntax? a then
      match archimedeanMkArg? b with
      | some x =>
        let x : TSyntax `term := ⟨x⟩
        `(($x → 0))
      | none => throw ()
    else
      throw ()
  | _ =>
    throw ()

