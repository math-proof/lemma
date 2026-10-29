import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Structure.Lean.Expr.Part2
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def UnaryPrefix.func : UnaryPrefix → Func
  | ⟨name⟩ =>
    match name with
    | `Neg.neg => ⟨75, "-", "-"⟩  -- LeanNeg
    | `Not => ⟨40, "¬", "\\lnot"⟩  -- Lean_lnot
    | `Bool.not => ⟨40, "!", "\\text{!}"⟩  -- LeanNot
    | `Complement.complement => ⟨100, "~~~", "~~~"⟩
    | `Complex.conj => ⟨1024, "~", "\\overline"⟩  -- LeanConj, SymPy `~z` / `starRingEnd ℂ`
    | `Star.star => ⟨1024, "~", "\\overline"⟩  -- Mathlib star / conjugate
    | `Complex.ofReal
    | `Hyperreal.ofReal
    | `Int.ofNat
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Fin.val
    | `Finset.toSet
    | `Subtype.val => ⟨1024, "↑", "\\uparrow"⟩  -- Lean_uparrow, https://github.com/leanprover/lean4/blob/v4.23.0/src/Init/Coe.lean#L296
    | `DFunLike.coe => ⟨1024, "⇑", "\\Uparrow"⟩  -- LeanUparrow
    | `Real.sqrt
    | `Root.sqrt => ⟨72, "√", "\\sqrt"⟩  -- Lean_sqrt
    | `Root.cubic => ⟨72, "∛", "\\sqrt[3]"⟩
    | `Root.quartic => ⟨72, "∜", "\\sqrt[4]"⟩
    | `OfNat.ofNat => ⟨107, "cast", ""⟩  -- Lean_cast
    | _ => ⟨76, name.toString, name.toString⟩  -- UnaryPrefix resulted from Lean.Expr.proj


def UnaryPrefix.isProp : UnaryPrefix → Bool
  | ⟨`Not⟩ => true
  | _ => false


