module

public import Mathlib
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.MeasurabilityOfFunctions

public section

open MeasureTheory MeasureTheory.SimpleFunc
open scoped ENNReal NNReal


namespace SimpleApproximation

/--
[eapprox_uniform_on_bounded_strict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationUniform.lean)
-/
public theorem eapprox_uniform_on_bounded_strict
  [MeasurableSpace X]
  {f : X → ENNReal}
-- given
  (hf : Measurable f)
  (c : NNReal)
  (ε : ENNReal)
  (hε : 0 < ε) :
-- imply
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, f x ≤ ↑c → f x - SimpleFunc.eapprox f n x < ε := by
-- proof
  obtain ⟨N, hN⟩ := ennrealRatEmbed_dense_Icc (↑c) ENNReal.coe_ne_top ε hε
  exact ⟨N, fun n hn x hfx => by
    obtain ⟨k, hkN, hk_le, hk_diff⟩ := hN (f x) hfx
    have hkn : k < n := Nat.lt_of_lt_of_le hkN hn
    have heapprox_ge : ennrealRatEmbed k ≤ SimpleFunc.eapprox f n x := by
      simp only [SimpleFunc.eapprox, SimpleFunc.approx_apply x hf]
      exact Finset.le_sup_of_le (Finset.mem_range.mpr hkn) (ite_eq_left hk_le ▸ le_refl _)
    calc f x - SimpleFunc.eapprox f n x
      ≤ f x - ennrealRatEmbed k := tsub_le_tsub_left heapprox_ge _
      _ < ε := hk_diff⟩

end SimpleApproximation


-- created on 2026-10-23
-- updated on 2026-11-15
