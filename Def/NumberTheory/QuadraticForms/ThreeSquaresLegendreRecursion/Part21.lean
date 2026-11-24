module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part17


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def r3leg_scaledIncOrthEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legIntVec) :
    {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} ≃
      {w : r3legOrthCone p (r3legRed p x) // (w.1 : r3legModVec p) ≠ 0} where
  toFun w := ⟨⟨w.1.1, w.1.2.2, by
    rw [r3leg_b_comm]
    exact (r3leg_inc_scale_iff hp3 w.1 x).mp w.2⟩, w.1.2.1⟩
  invFun w := ⟨⟨w.1.1, w.2, w.1.2.1⟩, by
    apply (r3leg_inc_scale_iff hp3 _ x).mpr
    rw [r3leg_b_comm]
    exact w.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end MetaMathlibExt
