/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part6


namespace MetaMathlibExt

noncomputable def r3leg_planeEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (x : r3legModVec p) (hx : x.2 ≠ 0) :
    ZMod p × ZMod p ≃ r3legPlane p x where
  toFun z := ⟨((z.1, z.2), -(x.1.1 * z.1 + x.1.2 * z.2) / x.2), by
    dsimp [r3legB]
    field_simp [hx]
    ring⟩
  invFun w := (w.1.1.1, w.1.1.2)
  left_inv z := rfl
  right_inv w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply (div_eq_iff hx).mpr
      have hw := w.2
      dsimp [r3legB] at hw
      linear_combination -hw

def r3leg_planeOrthEquiv {p : ℕ} (x : r3legModVec p) :
    {w : r3legPlane p x // r3legQ (w : r3legModVec p) = 0} ≃
      r3legOrthCone p x where
  toFun w := ⟨w.1, w.2, w.1.2⟩
  invFun w := ⟨⟨w.1, w.2.2⟩, w.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def r3leg_binaryOrthEquiv {p : ℕ} [Fact (Nat.Prime p)]
    (x : r3legModVec p) (hx : x.2 ≠ 0) :
    r3legBinaryZeros p (x.1.1 ^ 2 + x.2 ^ 2) (x.1.1 * x.1.2)
        (x.1.2 ^ 2 + x.2 ^ 2) ≃ r3legOrthCone p x := by
  let e : r3legBinaryZeros p (x.1.1 ^ 2 + x.2 ^ 2) (x.1.1 * x.1.2)
      (x.1.2 ^ 2 + x.2 ^ 2) ≃
      {w : r3legPlane p x // r3legQ (w : r3legModVec p) = 0} :=
    Equiv.subtypeEquiv (r3leg_planeEquiv x hx) (fun z => by
      let w : r3legModVec p :=
        ((z.1, z.2), -(x.1.1 * z.1 + x.1.2 * z.2) / x.2)
      have hid : x.2 ^ 2 * r3legQ w =
          (x.1.1 ^ 2 + x.2 ^ 2) * z.1 ^ 2 +
            2 * (x.1.1 * x.1.2) * z.1 * z.2 +
            (x.1.2 ^ 2 + x.2 ^ 2) * z.2 ^ 2 := by
        dsimp [w, r3legQ]
        field_simp [hx]
        ring
      change (x.1.1 ^ 2 + x.2 ^ 2) * z.1 ^ 2 +
          2 * (x.1.1 * x.1.2) * z.1 * z.2 +
          (x.1.2 ^ 2 + x.2 ^ 2) * z.2 ^ 2 = 0 ↔ r3legQ w = 0
      constructor
      · intro h
        have h' : x.2 ^ 2 * r3legQ w = 0 := by rw [hid, h]
        exact (mul_eq_zero.mp h').resolve_left (pow_ne_zero 2 hx)
      · intro h
        rw [← hid, h, mul_zero])
  exact e.trans (r3leg_planeOrthEquiv x)

end MetaMathlibExt
