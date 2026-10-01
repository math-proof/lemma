import Lemma.Tensor.SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block
import sympy.Basic
open Tensor Hyperreal


/--
py: `softmax(Q @ K.T + V + (Bool(i < d[j]) - 1) * oo) = V` with the relative-position bias
`V[i, j] = w_V[k + clip(r[d[j]] - r[i], -k, k)]` (here `c = k`, `dm = d`, `wV = w_V`), in the hyperreal masked softmax.
For each feature `t` the logits are \( a_{ij} = \langle Q_i, K_j \rangle + V_{ij}^{t} \) and the mask is \( \Xi_{ij} = [i < d_j] \):
\[
\operatorname{softmax}(a + (\Xi - 1)\infty) \approx V^{t}.
\]
The py statement (`@prove(proved=False)`) is false as stated: the left side is a probability distribution supported on
`{ j | i < d_j }`, while `V` is an arbitrary table lookup of `w_V`.
Besides the py hypotheses (`_h₀`, `_h₁`) we therefore assume exactly what makes the equation a fixed-point identity:
`h_ne` (every query has a visible key, so the masked softmax is defined),
`h_mask` (masked entries of `V` are `0`) and `h_fix` (on the visible entries
\( V_{ij} \sum_{k : i < d_k} e^{a_{ik}} = e^{a_{ij}} \)).
-/
@[main]
private lemma relative_distance.lower_triangle
  {n m d_z : ℕ}
  {dm : Fin m → Fin n}
  {c : ℤ}
  {r : Fin n → ℤ}
  {wV : ℤ → Fin d_z → ℝ}
  {Q : Fin n → Fin d_z → ℝ}
  {K : Fin m → Fin d_z → ℝ}
  {V : Fin n → Fin m → Fin d_z → ℝ}
-- given
  (_h₀ : (Finset.univ.image dm).card = m)
  (_h₁ : ∀ i j t, V i j t = wV (c + max (-c) (min (r (dm j) - r i) c)) t)
  (h_ne : ∀ i : Fin n, ∃ j : Fin m, i.val < (dm j).val)
  (h_mask : ∀ i j t (_ : (dm j).val ≤ i.val), V i j t = 0)
  (h_fix : ∀ i j t (_ : i.val < (dm j).val),
    V i j t = Real.exp ((∑ s, Q i s * K j s) + V i j t) /
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => i.val < (dm k).val), Real.exp ((∑ s, Q i s * K k s) + V i k t)) :
-- imply
  ∀ t : Fin d_z,
    let Ξ : Tensor ℝ* [n, m] := [i < n] [j < m] (Bool.toNat (decide (i.val < (dm j).val)))
    let A : Tensor ℝ* [n, m] :=
      ([i < n] [j < m] (((∑ s, Q i s * K j s) + V i j t : ℝ) : Tensor ℝ []) : Tensor ℝ [n, m])
    (A + (Ξ - 1) * ∞).softmax ≈ (([i < n] [j < m] ((V i j t : ℝ) : Tensor ℝ []) : Tensor ℝ [n, m]) : Tensor ℝ* [n, m]) := by
-- proof
  intro t
  have h := SoftmaxAdd_Mul_Infty.eq.Cast_Stack_Ite_Block (n := n) (m := m)
    (fun i j => i.val < (dm j).val) (fun i j => (∑ s, Q i s * K j s) + V i j t) (fun i j => V i j t) h_ne
    (fun i j hp => h_fix i j t hp)
  refine h.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  by_cases hp : i.val < (dm j).val
  · simp only [hp, if_true]
  · simp only [hp, if_false, h_mask i j t (not_lt.mp hp)]


-- created on 2022-04-26
