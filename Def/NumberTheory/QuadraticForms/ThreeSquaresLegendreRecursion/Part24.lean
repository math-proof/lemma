module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part21


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def r3leg_incidenceSwap {p n : ℕ} [Fact (Nat.Prime p)] (hp3 : 3 ≤ p) :
    (Σ w : r3legIso p,
      {y : r3legRepType (p ^ 2 * n) // r3legInc hp3 w y}) ≃
    (Σ y : r3legRepType (p ^ 2 * n),
      {w : r3legIso p // r3legInc hp3 w y}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
