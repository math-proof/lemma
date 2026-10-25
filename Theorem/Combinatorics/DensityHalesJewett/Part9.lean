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
import Def.Combinatorics.DensityHalesJewett.Part10
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhj_corollary11_cube {k m : ℕ} {δ η θ γ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hθ : 0 < θ) (hθle : θ ≤ 1) (hη : η = δ * θ / 48)
    (hγ : γ = δ * η ^ 2 / k)
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ η)
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B)
    (hden : δ - 2 * η ≤ dhjDensity B)
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    ∃ D : Fin k → Finset (Fin m → Fin (k + 1)),
      (∀ i, dhjInsensitive i (D i)) ∧
        γ ≤ dhjDensity (dhjFamilyMeet D) ∧
        (δ + γ) * dhjDensity (dhjFamilyMeet D) ≤
          dhjDensity (B ∩ dhjFamilyMeet D) := by
  classical
  obtain ⟨hC, hCi, hCeq, hdiff, hcorr⟩ :=
    dhj_lemma10_cube hk hm hδ hθ.le hη hratio B hB hden hgood
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηle : η ≤ δ / 48 := by
    rw [hη]
    gcongr
    exact mul_le_of_le_one_right hδ.le hθle
  have hδ3η : 0 < δ - 3 * η := by
    nlinarith
  let Q : Finset (Fin m → Fin (k + 1)) := Finset.univ \ dhjCore B
  have hBQ : B ∩ Q = B \ dhjCore B := by
    ext x
    simp [Q]
  have hBQsub : B \ dhjCore B ⊆ Q := by
    intro x hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hQlower : δ - 3 * η ≤ dhjDensity Q :=
    hdiff.trans (dhjDensity_mono hBQsub)
  have hQpos : 0 < dhjDensity Q := hδ3η.trans_le hQlower
  let i₀ : Fin k := ⟨0, hk⟩
  obtain ⟨i, hiMass, hiCorr⟩ := dhj_exists_large_correlated_fiber hk B Q
    (dhjFirstBad i₀ B) hδ hηpos hQpos (by simpa [hBQ] using hcorr)
  have hfiber : dhjFiber Q (dhjFirstBad i₀ B) i = dhjCell B i := by
    exact dhj_fiber_firstBad_eq_cell i₀ B i
  rw [hfiber] at hiMass hiCorr
  let D := dhjCellFactor B i
  have hmeet : dhjFamilyMeet D = dhjCell B i := dhj_familyMeet_cellFactor B i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hηone : η ≤ 1 := hηle.trans (by linarith)
  have hγle3η : γ ≤ 3 * η := by
    rw [hγ]
    rw [div_le_iff₀ hkR]
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonneg hδ.le (sq_nonneg η)]
  have hγmass : γ ≤ dhjDensity (dhjCell B i) := by
    have hnum : δ * η ^ 2 ≤ 3 * η * (δ - 3 * η) := by
      nlinarith [mul_nonneg hδ.le (sq_nonneg η)]
    calc
      γ = δ * η ^ 2 / k := hγ
      _ ≤ (3 * η * (δ - 3 * η)) / k :=
        (div_le_div_iff_of_pos_right hkR).mpr hnum
      _ = (3 * η / k) * (δ - 3 * η) := by ring
      _ ≤ (3 * η / k) * dhjDensity Q := by gcongr
      _ ≤ dhjDensity (dhjCell B i) := hiMass
  refine ⟨D, fun j => dhj_cellFactor_insensitive B i j, ?_, ?_⟩
  · rwa [hmeet]
  · rw [hmeet]
    calc
      (δ + γ) * dhjDensity (dhjCell B i) ≤
          (δ + 3 * η) * dhjDensity (dhjCell B i) := by
        gcongr
        exact dhjDensity_nonneg _
      _ ≤ dhjDensity (B ∩ dhjCell B i) := hiCorr

end MathlibExt.Combinatorics.DensityHalesJewettWanted
