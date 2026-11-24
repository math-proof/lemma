module
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Def.NumberTheory.QuadraticForms.ThreeSquares
public import Theorem.Nat.QuadraticForms.ThreeSquares
public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.FieldTheory.Finite.Basic
public import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part14


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

def r3leg_rotOrthEquiv {p : ℕ} (x : r3legModVec p) :
    r3legOrthCone p x ≃ r3legOrthCone p (r3legRot x) :=
  Equiv.subtypeEquiv r3legRot (fun w => by
    constructor
    · rintro ⟨hq, hb⟩
      exact ⟨by rw [r3leg_q_rot, hq], by rw [r3leg_b_rot, hb]⟩
    · rintro ⟨hq, hb⟩
      exact ⟨by rw [r3leg_q_rot] at hq; exact hq,
        by rw [r3leg_b_rot] at hb; exact hb⟩)

end MetaMathlibExt
