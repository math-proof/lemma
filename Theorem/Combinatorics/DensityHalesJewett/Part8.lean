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
import Def.Combinatorics.DensityHalesJewett.Part9
/-! Proves the density Hales–Jewett theorem and the Graham–Rothschild theorem for lines. -/


namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

open scoped Finset

end MathlibExt.Combinatorics.DensityHalesJewettWanted

namespace MathlibExt.Combinatorics.DensityHalesJewettWanted

theorem dhjLineTop_injective {k : ℕ} {ι : Type*} :
    Function.Injective (dhjLineTop : Combinatorics.Line (Fin k) ι → ι → Fin (k + 1)) := by
  intro l l' h
  rw [← dhjLineOfTop_lineTop l, ← dhjLineOfTop_lineTop l']
  congr

theorem dhj_lineFree_inter_core_noLast {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B) :
    ∀ x ∈ B ∩ dhjCore B, ∀ q, x q ≠ Fin.last k := by
  classical
  intro x hx q hxq
  have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
  have hxC : x ∈ dhjCore B := (Finset.mem_inter.mp hx).2
  have hxlast : dhjHasLast x := by
    rw [dhjHasLast]
    intro h
    exact h q hxq
  let l := dhjLineOfTop x hxlast
  apply hB (dhjLiftLine l)
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have htop : dhjLineTop l = x := dhjLineTop_lineOfTop x hxlast
    change dhjLineTop l ∈ B
    rw [htop]
    exact hxB
  · rw [dhjLiftLine_apply]
    have hreplace : dhjReplaceLast i x = Fin.castSucc ∘ l i := by
      rw [← dhjLineTop_lineOfTop x hxlast]
      exact dhjReplaceLast_lineTop i l
    rw [← hreplace]
    exact (dhj_mem_core B x).mp hxC i

theorem dhj_inter_core_density_le_ratio {k m : ℕ}
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B) :
    dhjDensity (B ∩ dhjCore B) ≤ ((k : ℝ) / (k + 1)) ^ m := by
  classical
  let S : Finset (Fin m → Fin (k + 1)) :=
    Finset.univ.filter fun x => ∀ q, x q ≠ Fin.last k
  have hsub : B ∩ dhjCore B ⊆ S := by
    intro x hx
    simpa [S] using dhj_lineFree_inter_core_noLast B hB x hx
  apply (dhjDensity_mono hsub).trans_eq
  rw [dhjDensity]
  have hcardS : S.card = k ^ m := by
    rw [show S.card = Fintype.card {x : Fin m → Fin (k + 1) //
        ∀ q, x q ≠ Fin.last k} by
      rw [Fintype.card_subtype]]
    rw [Fintype.card_congr (dhjNoLastEquiv (k := k) (ι := Fin m))]
    simp
  rw [hcardS]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [div_pow]
  norm_num

theorem dhj_lemma10_cube {k m : ℕ} {δ η θ : ℝ}
    (hk : 0 < k) (hm : k ≤ m) (hδ : 0 < δ) (hθ : 0 ≤ θ)
    (hη : η = δ * θ / 48)
    (hratio : ((k : ℝ) / (k + 1)) ^ m ≤ η)
    (B : Finset (Fin m → Fin (k + 1))) (hB : dhjLineFree B)
    (hden : δ - 2 * η ≤ dhjDensity B)
    (hgood : θ / 2 ≤ dhjDensity (dhjGoodRestrictedLines B)) :
    let C := dhjCore B
    θ / 4 ≤ dhjDensity C ∧
      (∀ i : Fin k, dhjInsensitive i (dhjInsensitivePreimage B i)) ∧
      (∀ x, x ∈ C ↔ ∀ i : Fin k, x ∈ dhjInsensitivePreimage B i) ∧
      δ - 3 * η ≤ dhjDensity (B \ C) ∧
      (δ + 6 * η) * dhjDensity (Finset.univ \ C) ≤ dhjDensity (B \ C) := by
  classical
  dsimp only
  have hC : θ / 4 ≤ dhjDensity (dhjCore B) :=
    dhj_core_density_lower hk hm hθ B hgood
  have hBC : dhjDensity (B ∩ dhjCore B) ≤ η :=
    (dhj_inter_core_density_le_ratio B hB).trans hratio
  have hpartition := dhj_density_inter_add_sdiff B (dhjCore B)
  have hdiff : δ - 3 * η ≤ dhjDensity (B \ dhjCore B) := by
    linarith
  have hcomp : dhjDensity (Finset.univ \ dhjCore B) =
      1 - dhjDensity (dhjCore B) := dhj_density_compl (dhjCore B)
  have hcompUpper : dhjDensity (Finset.univ \ dhjCore B) ≤ 1 - θ / 4 := by
    rw [hcomp]
    linarith
  have hηnonneg : 0 ≤ η := by rw [hη]; positivity
  have hcoef : 0 ≤ δ + 6 * η := by positivity
  have hnumeric : (δ + 6 * η) * (1 - θ / 4) ≤ δ - 3 * η := by
    rw [hη]
    nlinarith [mul_nonneg hδ.le (sq_nonneg θ)]
  refine ⟨hC, fun i => dhjInsensitive_preimage B i,
    fun x => dhj_mem_core_iff_preimages B x, hdiff, ?_⟩
  calc
    (δ + 6 * η) * dhjDensity (Finset.univ \ dhjCore B) ≤
        (δ + 6 * η) * (1 - θ / 4) := mul_le_mul_of_nonneg_left hcompUpper hcoef
    _ ≤ δ - 3 * η := hnumeric
    _ ≤ dhjDensity (B \ dhjCore B) := hdiff

end MathlibExt.Combinatorics.DensityHalesJewettWanted
