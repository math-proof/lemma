import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BellPolynomialConvolutionRecurrence
open PowerSeries
open MetaMathlibExt


/--
[bell_convolution_linear_recurrence_of_charZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellPolynomialConvolutionRecurrence.lean)
-/
@[path]
private lemma bell_convolution_linear_recurrence_of_charZero_eq
  [Field K] [CharZero K]
  {c y : ℕ → K}
  {r n : ℕ}
-- given
  (hr : 0 < r)
  (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : K) * ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)), ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : K)))
  (hn : 1 ≤ n) :
-- imply
  let conv : ℕ → K := by
-- proof
  apply MetaMathlibExt.bell_convolution_linear_recurrence_of_charZero c y r hr hBell n hn

/--
[bell_convolution_linear_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellPolynomialConvolutionRecurrence.lean)
-/
@[path]
private lemma bell_convolution_linear_recurrence_eq
  [Field K] [CharZero K]
  {c y : ℕ → ℝ}
  {r n : ℕ}
-- given
  (hr : 0 < r)
  (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : ℝ) * ∑ j ∈ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.range (n + 1))).filter (fun j => (∑ i, j i = k) ∧ (∑ i, (i.val + 1) * j i = n)), ∏ i, ((c (i.val + 1)) ^ (j i) / (((j i).factorial : ℕ) : ℝ)))
  (hn : 1 ≤ n) :
-- imply
  let conv : ℕ → ℝ := by
-- proof
  apply MetaMathlibExt.bell_convolution_linear_recurrence c y r hr hBell n hn

/--
[bell_convolution_linear_recurrence_partialBellPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellPolynomialConvolutionRecurrence.lean)
-/
@[path]
private lemma bell_convolution_linear_recurrence_partialBellPolynomial_eq
  [Field K] [CharZero K]
  {c y : ℕ → K}
  {r n : ℕ}
-- given
  (hr : 0 < r)
  (hBell : ∀ n : ℕ, y n = ∑ k ∈ Finset.range (n + 1), (k.factorial : K) / n.factorial * partialBellPolynomial n k (fun m => (m.factorial : K) * c m))
  (hn : 1 ≤ n) :
-- imply
  let conv : ℕ → K := by
-- proof
  apply MetaMathlibExt.bell_convolution_linear_recurrence_partialBellPolynomial c y r hr hBell n hn


-- created on 2026-10-20
