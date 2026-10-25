/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/DensityHalesJewett.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Def.Combinatorics.DensityHalesJewett.Part8
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhj_lineFree_card_le_middle {n : ℕ} (A : Finset (Fin n → Fin 2))
    (hA : dhjLineFree A) : A.card ≤ n.choose (n / 2) := by
  classical
  have hsperner := (dhj_supports_antichain A hA).sperner
  rw [Finset.card_image_of_injective A dhjSupport_injective] at hsperner
  simpa using hsperner

theorem dhj_lineFree_density_le_central (r : ℕ)
    (A : Finset (Fin (2 * r) → Fin 2)) (hA : dhjLineFree A) :
    dhjDensity A ≤ (Nat.centralBinom r : ℝ) / 4 ^ r := by
  have hcard : A.card ≤ Nat.centralBinom r := by
    simpa [Nat.centralBinom, Nat.mul_div_cancel_left] using dhj_lineFree_card_le_middle A hA
  have hcube : Fintype.card (Fin (2 * r) → Fin 2) = 4 ^ r := by
    simp [pow_mul]
  rw [dhjDensity, hcube]
  rw [Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast hcard

theorem dhjThreshold_two {δ : ℝ} (hδ : 0 < δ) : dhjThreshold 2 δ := by
  obtain ⟨r, hr⟩ := dhj_exists_centralBinom_ratio_lt hδ
  apply dhjThreshold_of_at (k := 2) (N := 2 * r) (by omega)
  intro A hden
  by_contra hline
  have hfree : dhjLineFree A := by
    intro l hl
    exact hline ⟨l, hl⟩
  have hupper := dhj_lineFree_density_le_central r A hfree
  linarith

end MathlibExt.Combinatorics.DensityHalesJewettWanted
