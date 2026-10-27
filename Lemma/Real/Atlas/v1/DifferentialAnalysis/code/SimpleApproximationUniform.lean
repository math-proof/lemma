import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory MeasureTheory.SimpleFunc
open scoped ENNReal NNReal


namespace SimpleApproximation

/--
[eapprox_uniform_on_bounded_strict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SimpleApproximationUniform.lean)
-/
@[path]
lemma eapprox_uniform_on_bounded_strict
  [MeasurableSpace X]
  {f : X → ℝ≥0∞}
-- given
  (hf : Measurable f)
  (c : ℝ≥0)
  (ε : ℝ≥0∞)
  (hε : 0 < ε) :
-- imply
  ∃ N : ℕ, ∀ n, N ≤ n → ∀ x, f x ≤ ↑c → f x - SimpleFunc.eapprox f n x < ε := by
-- proof
  obtain ⟨N, hN⟩ := ennrealRatEmbed_dense_Icc (↑c) ENNReal.coe_ne_top ε hε
  exact ⟨N, fun n hn x hfx => by
    obtain ⟨k, hkN, hk_le, hk_diff⟩ := hN (f x) hfx
    have hkn : k < n := Nat.lt_of_lt_of_le hkN hn
    have heapprox_ge : ennrealRatEmbed k ≤ SimpleFunc.eapprox f n x :=
      eapprox_ge_ennrealRatEmbed hf hkn x hk_le
    calc f x - SimpleFunc.eapprox f n x
      ≤ f x - ennrealRatEmbed k := tsub_le_tsub_left heapprox_ge _
      _ < ε := hk_diff⟩

end SimpleApproximation


-- created on 2026-10-23
