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
import Def.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part22


namespace MetaMathlibExt

lemma r3leg_sq_dvd_of_red_eq_zero {p n : ℕ} (x : r3legRepType n)
    (hx : r3legRed p (x : r3legIntVec) = 0) : p ^ 2 ∣ n := by
  have hdiv := (r3leg_vecDvd_iff_red_eq_zero p x).mpr hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, c, hc⟩ := hdiv
  apply Int.natCast_dvd_natCast.mp
  change (p : ℤ) ^ 2 ∣ (n : ℤ)
  rw [← r3leg_mem_rep.mp x.2]
  refine ⟨a ^ 2 + b ^ 2 + c ^ 2, ?_⟩
  simp only [r3legQ]
  rw [ha, hb, hc]
  ring

lemma r3leg_zeroRed_rep_card_of_not_dvd {p n : ℕ} [Fact (Nat.Prime p)]
    (hdiv : ¬p ^ 2 ∣ n) :
    Fintype.card {x : r3legRepType n // r3legRed p (x : r3legIntVec) = 0} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun x => hdiv (r3leg_sq_dvd_of_red_eq_zero x.1 x.2)⟩

lemma r3leg_zeroRed_rep_card {p n : ℕ} [Fact (Nat.Prime p)] :
    Fintype.card {x : r3legRepType n // r3legRed p (x : r3legIntVec) = 0} =
      if p ^ 2 ∣ n then Nat.threeSquareRepresentationCount (n / p ^ 2) else 0 := by
  split_ifs with h
  · exact r3leg_zeroRed_rep_card_of_dvd h
  · exact r3leg_zeroRed_rep_card_of_not_dvd h

end MetaMathlibExt
