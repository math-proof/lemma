import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.ModularCurve_LegendreJ
import Lemma.Int.P2MUtil


namespace Definitions
end Definitions
open Definitions
open Polynomial
open WeierstrassCurve
open ModularCurve
open Int


private lemma natDegree_legendreFibrePoly {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (j : K) :
  (C (256 : K) * (X ^ 2 - X + 1) ^ 3 - C j * (X ^ 2 * (X - 1) ^ 2)).natDegree = 6 := by
  have h256 : (256 : K) ≠ 0 := by
    rw [show (256 : K) = 2 ^ 8 by norm_num]; exact pow_ne_zero _ h2
  compute_degree!

private lemma exists_legendreJ_eq' {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (j : K) :
  ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ legendreJ t = j := by
  set F : K[X] := C (256 : K) * (X ^ 2 - X + 1) ^ 3 - C j * (X ^ 2 * (X - 1) ^ 2) with hF
  have h256 : (256 : K) ≠ 0 := by
    rw [show (256 : K) = 2 ^ 8 by norm_num]; exact pow_ne_zero _ h2
  have hF6 : F.natDegree = 6 := natDegree_legendreFibrePoly h2 j
  have hF0 : F ≠ 0 := by
    rintro h; rw [h, natDegree_zero] at hF6; exact absurd hF6 (by norm_num)
  have hdeg : F.degree ≠ 0 := by
    rw [degree_eq_natDegree hF0, hF6]; exact_mod_cast (by norm_num : (6 : ℕ) ≠ 0)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root F hdeg
  have ht' : 256 * (t ^ 2 - t + 1) ^ 3 - j * (t ^ 2 * (t - 1) ^ 2) = 0 := by
    have := ht.eq_zero
    simpa [hF] using this
  have ht0 : t ≠ 0 := by rintro rfl; apply h256; linear_combination ht'
  have ht1 : t ≠ 1 := by rintro rfl; apply h256; linear_combination ht'
  refine ⟨t, ht0, ht1, ?_⟩
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  rw [legendreJ, div_eq_iff hden]
  linear_combination ht'

p2m_open "Polynomial ModularCurve P2MW.S_ModularCurve_exists_legendreJ_eq.ModularCurve"
/--
[ModularCurve_exists_legendreJ_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_legendreJ_eq.lean)
-/
@[path]
private lemma main
  [Field K] [IsAlgClosed K]
  {j : K}
-- given
  (h0 : (2 : K) ≠ 0) :
-- imply
  ∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ legendreJ t = j :=
-- proof
  exists_legendreJ_eq' h0 j


-- created on 2026-10-24
