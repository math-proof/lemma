import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Gather
import sympy.concrete.expr_with_limits
import Lemma.Fin.SumFilter.eq.Sum
import Lemma.Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0
import Lemma.Fin.SumFilter.eq.Sum.of.All_Le.EqEMod.Lt.Gt_0
open Tensor
set_option maxHeartbeats 2000000


/--
Window form of the hyperreal masked softmax for the band \( i - l < j < i + u \): with \( \beta = \operatorname{relu}(i - l + 1) \) and \( \zeta = \min(n, i + u) \),
\[
\operatorname{softmax}(a + ([i - l < j < i + u] - 1)\infty)_i \, V_i \approx
\Bigl[ \sum_{t < \zeta - \beta} \frac{e^{a_{i, \beta + t}}}{\sum_{s < \zeta - \beta} e^{a_{i, \beta + s}}}\, v_{i, \beta + t, \ell} \Bigr]_\ell .
\]
-/
@[main]
private lemma window
  {n d l u : ℕ}
-- given
  (h_l : 0 < l)
  (h_u : 0 < u)
  (a : Fin n → Fin n → ℝ)
  (v : Fin n → Fin n → Fin d → ℝ)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u))))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (a i j : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d] := [j < n] [s < d] (v i j s : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d]) ≈
    ((([t < d] ((∑ j' : Fin (min n (i.val + u) - (i.val + 1 - l)),
        Real.exp (a i ⟨i.val + 1 - l + j', by have := j'.2; omega⟩) / (∑ k' : Fin (min n (i.val + u) - (i.val + 1 - l)), Real.exp (a i ⟨i.val + 1 - l + k', by have := k'.2; omega⟩)) *
          v i ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ t : ℝ) : Tensor ℝ [])) : Tensor ℝ [d]) : Tensor ℝ* [d]) := by
-- proof
  intro Ξ A Vᵢ
  exact DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Gather (fun i j => ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u)) a v
    (fun t : Fin (min n (i.val + u) - (i.val + 1 - l)) => (⟨i.val + 1 - l + t, by have := t.2; omega⟩ : Fin n))
    (fun i => ⟨i, ⟨by omega, by omega⟩⟩) i (fun g => Fin.SumFilter.eq.Sum i l u g)


/--
Dilated window form of the hyperreal masked softmax for the band \( i - l < j < i + u \), \( d \mid j - i \): the unmasked entries of row \( i \) are \( b + m d \) for \( m < \lceil (\min(n, i + u) - b) / d \rceil \), and
\[
\operatorname{softmax}(a + ([\ldots] - 1)\infty)_i \, V_i \approx
\Bigl[ \sum_{m} \frac{e^{a_{i, b + m d}}}{\sum_{m'} e^{a_{i, b + m' d}}}\, v_{i, b + m d, \ell} \Bigr]_\ell .
\]
-/
@[main]
private lemma dilated
  {n d_v l u d b : ℕ}
-- given
  (h_l : 0 < l)
  (h_u : 0 < u)
  (hd : 0 < d)
  (a : Fin n → Fin n → ℝ)
  (v : Fin n → Fin n → Fin d_v → ℝ)
  (i : Fin n)
  (hb1 : (i.val : ℤ) < b + l)
  (hb2 : ((b : ℤ) - i.val) % d = 0)
  (hb3 : ∀ j : ℕ, ((i.val : ℤ) < j + l) → (((j : ℤ) - i.val) % d = 0) → b ≤ j) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0))))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (a i j : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_v] := [j < n] [s < d_v] (v i j s : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_v]) ≈
    ((([t < d_v] ((∑ m : Fin ((min n (i.val + u) - b + d - 1) / d),
        Real.exp (a i ⟨b + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m.2; omega⟩) / (∑ m' : Fin ((min n (i.val + u) - b + d - 1) / d), Real.exp (a i ⟨b + m' * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m'.2; omega⟩)) *
          v i ⟨b + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m.2; omega⟩ t : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_v]) : Tensor ℝ* [d_v]) := by
-- proof
  intro Ξ A Vᵢ
  exact DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Gather (fun i j => ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0)) a v
    (fun m : Fin ((min n (i.val + u) - b + d - 1) / d) => (⟨b + m * d, by have := Nat.LtAdd_Mul.of.Lt_DivSubAddSub1.Gt_0 hd m.2; omega⟩ : Fin n))
    (fun i => ⟨i, ⟨by omega, by omega, by simp⟩⟩) i (fun g => Fin.SumFilter.eq.Sum.of.All_Le.EqEMod.Lt.Gt_0 i l u d b hd hb1 hb2 hb3 g)


-- created on 2026-10-01