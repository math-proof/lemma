import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.oc_boxcrossingscalesum
open Finset StatMech StatMech.Walls


/--
[oc_sum_reindex_le_card_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxcrossingscalesum.lean)
-/
@[path]
private lemma oc_sum_reindex_le_card_smul_eq
  [DecidableEq β]
  {S : Finset α}
  {φ : α → β}
  {g : β → ℝ}
  {T : Finset β}
  {C : ℕ}
-- given
  (hg : ∀ b, 0 ≤ g b)
  (himg : ∀ a ∈ S, φ a ∈ T)
  (hfib : ∀ b ∈ T, (S.filter (fun a => φ a = b)).card ≤ C) :
-- imply
  ∑ a ∈ S, g (φ a) ≤ (C : ℝ) * ∑ b ∈ T, g b := by
-- proof
  apply StatMech.Walls.oc_sum_reindex_le_card_smul S φ g hg T himg C hfib

/--
[oc_sum_translate_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxcrossingscalesum.lean)
-/
@[path]
private lemma oc_sum_translate_le_eq
  {n r : ℕ}
  {g : ℕ → ℝ}
-- given
  (hr : r ≤ n)
  (hg : ∀ j, 0 ≤ g j) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, g ((k : ℤ) - (r : ℤ)).natAbs ≤ 2 * ∑ j ∈ Finset.range (n + 1), g j := by
-- proof
  apply StatMech.Walls.oc_sum_translate_le n r hr g hg

/--
[oc_two_mul_le_two_mul_sup'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxcrossingscalesum.lean)
-/
@[path]
private lemma oc_two_mul_le_two_mul_sup'_eq
  {Λ : Finset α}
  {S : α → ℝ}
  {u : α}
-- given
  (hne : Λ.Nonempty)
  (hu : u ∈ Λ) :
-- imply
  2 * S u ≤ 2 * Λ.sup' hne S := by
-- proof
  apply StatMech.Walls.oc_two_mul_le_two_mul_sup' Λ hne S u hu

/--
[oc_revealment_sum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxcrossingscalesum.lean)
-/
@[path]
private lemma oc_revealment_sum_bound_eq
  {Λ : Finset α}
  {μ : α → ℕ → ℝ}
  {n r : ℕ}
  {u : α}
  {q : ℕ → ℝ}
-- given
  (hne : Λ.Nonempty)
  (hμ : ∀ x j, 0 ≤ μ x j)
  (hr : r ≤ n)
  (hu : u ∈ Λ)
  (hcomp : ∀ k, q k ≤ μ u ((k : ℤ) - (r : ℤ)).natAbs) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, q k ≤ 2 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) := by
-- proof
  apply StatMech.Walls.oc_revealment_sum_bound Λ hne μ hμ n r hr u hu q hcomp

/--
[oc_box_crossing_scale_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxcrossingscalesum.lean)
-/
@[path]
private lemma oc_box_crossing_scale_sum_eq
  {Λ : Finset α}
  {μ : α → ℕ → ℝ}
  {n ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hne : Λ.Nonempty)
  (hμ : ∀ x j, 0 ≤ μ x j)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ μ u ((k : ℤ) - (ru : ℤ)).natAbs)
  (hcompv : ∀ k, qv k ≤ μ v ((k : ℤ) - (rv : ℤ)).natAbs) :
-- imply
  ∑ k ∈ Finset.Icc 1 n, (qu k + qv k) ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), μ x j) := by
-- proof
  apply StatMech.Walls.oc_box_crossing_scale_sum Λ hne μ hμ n ru rv hru hrv u v hu hv qu qv hcompu hcompv

/--
[oc_eq_revealment_family_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_boxcrossingscalesum.lean)
-/
@[path]
private lemma oc_eq_revealment_family_sum_le_eq
  {Λ : Finset α}
  {μ : α → ℕ → ℝ}
  {n ru rv : ℕ}
  {u v : α}
  {qu qv : ℕ → ℝ}
-- given
  (hne : Λ.Nonempty)
  (hμ : ∀ x j, 0 ≤ μ x j)
  (hru : ru ≤ n)
  (hrv : rv ≤ n)
  (hu : u ∈ Λ)
  (hv : v ∈ Λ)
  (hcompu : ∀ k, qu k ≤ μ u ((k : ℤ) - (ru : ℤ)).natAbs)
  (hcompv : ∀ k, qv k ≤ μ v ((k : ℤ) - (rv : ℤ)).natAbs) :
-- imply
  oc_box_crossing_scale_sum Λ hne μ hμ n ru rv hru hrv u v hu hv qu qv hcompu hcompv = StatMech.OSSS.revealment_family_sum_le Λ hne μ hμ n ru rv hru hrv u v hu hv qu qv hcompu hcompv := by
-- proof
  apply StatMech.Walls.oc_eq_revealment_family_sum_le Λ hne μ hμ n ru rv hru hrv u v hu hv qu qv hcompu hcompv


-- created on 2026-10-23
