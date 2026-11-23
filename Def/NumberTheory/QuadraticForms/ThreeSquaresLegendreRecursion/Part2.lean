/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion

@[expose] public section

namespace MetaMathlibExt

def r3legAligned (p : ℕ) (q : Quaternion ℤ) (w : r3legModVec p) : Prop :=
  ∀ x, ∃ t : ZMod p, r3legRed p (r3legPhi q x) = t • w

end MetaMathlibExt
