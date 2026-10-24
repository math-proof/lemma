import Mathlib
import sympy.Basic
open Finset


namespace Real

/--
[sum_mul_log_sum_div_sum_le_sum_mul_log_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/LogSum.lean)
-/
@[path]
lemma sum_mul_log_sum_div_sum_le_sum_mul_log_div
  {s : Finset ι}
  {p q : ι → ℝ}
-- given
  (hp : ∀ i ∈ s, 0 ≤ p i)
  (hq : ∀ i ∈ s, 0 < q i) :
-- imply
  (∑ i ∈ s, p i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
    ≤ ∑ i ∈ s, p i * log (p i / q i) := by
-- proof
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  have hQ : 0 < ∑ i ∈ s, q i := sum_pos hq hs
  have hJ := convexOn_mul_log.map_sum_le (t := s) (w := fun i => q i / ∑ j ∈ s, q j)
    (p := fun i => p i / q i) (fun i hi => (div_pos (hq i hi) hQ).le)
    (by rw [← sum_div, div_self hQ.ne'])
    (fun i hi => Set.mem_Ici.2 (div_nonneg (hp i hi) (hq i hi).le))
  have h1 : ∑ i ∈ s, (q i / ∑ j ∈ s, q j) • (p i / q i)
    = (∑ i ∈ s, p i) / ∑ i ∈ s, q i := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    have := (hq i hi).ne'
    rw [smul_eq_mul]
    field_simp
  have h2 : ∑ i ∈ s, (q i / ∑ j ∈ s, q j) • (p i / q i * log (p i / q i))
    = (∑ i ∈ s, p i * log (p i / q i)) / ∑ i ∈ s, q i := by
    rw [sum_div]
    refine sum_congr rfl fun i hi => ?_
    have := (hq i hi).ne'
    rw [smul_eq_mul]
    field_simp
  simp only [h1, h2] at hJ
  rw [le_div_iff₀ hQ] at hJ
  calc (∑ i ∈ s, p i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
    = (∑ i ∈ s, p i) / (∑ i ∈ s, q i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
      * ∑ i ∈ s, q i := by field_simp
    _ ≤ _ := hJ

end Real


-- created on 2026-10-20
-- updated on 2026-10-23
