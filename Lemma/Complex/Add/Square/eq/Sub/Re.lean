import Lemma.Complex.SquareNormSum_Get.eq.AddSumS


@[path]
private lemma main
  {n : ℕ}
  {a : ℕ → ℂ} :
-- imply
  ∑ i ∈ Finset.range n, ‖a[i]‖ ^ 2 = ‖∑ i ∈ Finset.range n, a[i]‖ ^ 2 - ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, 2 * (~a[i] * a[j]).re := by
-- proof
  rw [Complex.SquareNormSum_Get.eq.AddSumS]
  ring


-- created on 2023-06-24
-- updated on 2026-11-23
