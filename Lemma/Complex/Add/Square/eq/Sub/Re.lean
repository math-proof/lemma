import Lemma.Complex.SquareNormSum_Get.eq.AddSumS
open Complex


@[path]
private lemma main
  {n : ℕ}
  {a : ℕ → ℂ} :
-- imply
  ∑ i < n, ‖a[i]‖² = ‖∑ i < n, a[i]‖² - ∑ i < n, ∑ j < i, 2 * (~a[i] * a[j]).re := by
-- proof
  rw [SquareNormSum_Get.eq.AddSumS]
  ring


-- created on 2023-06-24
-- updated on 2026-11-26
