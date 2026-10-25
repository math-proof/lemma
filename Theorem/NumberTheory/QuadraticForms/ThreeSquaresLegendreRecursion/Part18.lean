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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part21


namespace MetaMathlibExt

lemma r3leg_scaled_inc_card_of_ne {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legIntVec) (hx : r3legRed p x ≠ 0) :
    (Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} : ℤ) =
      ((p : ℤ) - 1) * (1 + quadraticChar (ZMod p) (-r3legQ (r3legRed p x))) := by
  let z : r3legOrthCone p (r3legRed p x) :=
    ⟨(0 : r3legModVec p), by simp [r3legQ, r3legB]⟩
  have hzero :
      Fintype.card
          {w : r3legOrthCone p (r3legRed p x) // (w.1 : r3legModVec p) = 0} = 1 := by
    calc
      Fintype.card
          {w : r3legOrthCone p (r3legRed p x) // (w.1 : r3legModVec p) = 0} =
          Fintype.card {w : r3legOrthCone p (r3legRed p x) // w = z} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun w => by
          simp [z, Subtype.ext_iff])
      _ = 1 := Fintype.card_subtype_eq z
  have hcard :
      Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} =
        Fintype.card (r3legOrthCone p (r3legRed p x)) - 1 := by
    rw [Fintype.card_congr (r3leg_scaledIncOrthEquiv hp3 x),
      Fintype.card_subtype_compl, hzero]
  have hpos : 0 < Fintype.card (r3legOrthCone p (r3legRed p x)) :=
    Fintype.card_pos_iff.mpr ⟨z⟩
  have hcard' :
      Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} + 1 =
        Fintype.card (r3legOrthCone p (r3legRed p x)) := by
    omega
  have hcardz :
      (Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} : ℤ) + 1 =
        Fintype.card (r3legOrthCone p (r3legRed p x)) := by
    exact_mod_cast hcard'
  have horth := r3leg_orthCone_card hp3 (r3legRed p x) hx
  calc
    (Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} : ℤ) =
        (Fintype.card (r3legOrthCone p (r3legRed p x)) : ℤ) - 1 := by
      omega
    _ = (p : ℤ) + ((p : ℤ) - 1) *
          quadraticChar (ZMod p) (-r3legQ (r3legRed p x)) - 1 := by rw [horth]
    _ = ((p : ℤ) - 1) *
          (1 + quadraticChar (ZMod p) (-r3legQ (r3legRed p x))) := by ring

lemma r3leg_scaled_inc_card_of_eq {p : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (x : r3legIntVec) (hx : r3legRed p x = 0) :
    Fintype.card {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} = p ^ 2 - 1 := by
  let e : {w : r3legIso p // r3legInc hp3 w (r3legScale p x)} ≃ r3legIso p :=
    { toFun := fun w => w.1
      invFun := fun w => ⟨w, (r3leg_inc_scale_iff hp3 w x).mpr (by
        rw [hx]
        simp [r3legB])⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, r3leg_iso_card]

end MetaMathlibExt
