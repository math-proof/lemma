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
import Instance.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion


namespace MetaMathlibExt

lemma r3leg_primitiveUnitMap_surjective {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    Function.Surjective (r3leg_primitiveUnitMap hp3 y hyq hyne) := by
  intro w
  obtain ⟨κ, hκ, hyred⟩ := (r3leg_inc_primitive_iff hp3 w.1 y hyq hyne).mp w.2
  let u : (ZMod p)ˣ := Units.mk0 κ hκ
  refine ⟨u⁻¹, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((u⁻¹ : (ZMod p)ˣ) : ZMod p) • r3legRed p y = (w.1.1 : r3legModVec p)
  change r3legRed p y = (u : ZMod p) • (w.1.1 : r3legModVec p) at hyred
  rw [hyred, smul_smul, Units.inv_mul, one_smul]

lemma r3leg_primitive_inc_card {p n : ℕ} [Fact (Nat.Prime p)]
    (hp3 : 3 ≤ p) (y : r3legIntVec) (hyq : r3legQ y = (p ^ 2 * n : ℕ))
    (hyne : r3legRed p y ≠ 0) :
    Fintype.card {w : r3legIso p // r3legInc hp3 w y} = p - 1 := by
  let e := Equiv.ofBijective (r3leg_primitiveUnitMap hp3 y hyq hyne)
    ⟨r3leg_primitiveUnitMap_injective hp3 y hyq hyne,
      r3leg_primitiveUnitMap_surjective hp3 y hyq hyne⟩
  calc
    Fintype.card {w : r3legIso p // r3legInc hp3 w y} =
        Fintype.card (ZMod p)ˣ := (Fintype.card_congr e).symm
    _ = p - 1 := by rw [Fintype.card_units, ZMod.card]

lemma r3leg_b_comm {R : Type*} [CommSemiring R] (x y : (R × R) × R) :
    r3legB x y = r3legB y x := by
  simp [r3legB]
  ring

end MetaMathlibExt
