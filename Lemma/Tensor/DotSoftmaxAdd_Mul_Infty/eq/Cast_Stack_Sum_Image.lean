import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Ite_Mul
open Tensor
set_option maxHeartbeats 2000000


private lemma sum_image
  {n m : ℕ}
  {dm : Fin m → Fin n}
  (h : (Finset.univ.image dm).card = m)
  (f : Fin n → ℝ) :
  ∑ k ∈ Finset.univ.image dm, f k = ∑ j, f (dm j) := by
  have hd : Set.InjOn dm (Finset.univ : Finset (Fin m)) := by
    rw [← Finset.card_image_iff, h, Finset.card_univ, Fintype.card_fin]
  exact Finset.sum_image (fun x hx y hy hxy => hd (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy)


private lemma key
  {n m : ℕ}
  {dm : Fin m → Fin n}
  (h : (Finset.univ.image dm).card = m)
  (a : Fin n → ℝ)
  (a' : Fin m → ℝ)
  (v : Fin n → ℝ)
  (v' : Fin m → ℝ)
  (h_a : ∀ j, a (dm j) = a' j)
  (h_v : ∀ j, v (dm j) = v' j) :
  ∑ j, (if j ∈ Finset.univ.image dm then Real.exp (a j) / ∑ k ∈ Finset.univ.filter (fun k => k ∈ Finset.univ.image dm), Real.exp (a k) else 0) * v j =
    ∑ j, Real.exp (a' j) / (∑ k, Real.exp (a' k)) * v' j := by
  have hS : (∑ k ∈ Finset.univ.filter (fun k => k ∈ Finset.univ.image dm), Real.exp (a k)) = ∑ k, Real.exp (a' k) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, sum_image h]
    simp only [h_a]
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, hS]
  rw [sum_image h (fun j => Real.exp (a j) / (∑ k, Real.exp (a' k)) * v j)]
  simp only [h_a, h_v]


open Hyperreal


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]


private lemma ne_row
  {n m : ℕ}
  {dm : Fin m → Fin n}
  (h_m : 0 < m) :
  ∀ _ : Fin n, ∃ j : Fin n, j ∈ Finset.univ.image dm := by
  intro _
  exact ⟨dm ⟨0, h_m⟩, Finset.mem_image_of_mem dm (Finset.mem_univ _)⟩


/--
Gathered form of the hyperreal masked softmax, row by row. The mask keeps exactly the \( m \) distinct columns \( d_0, \dots, d_{m-1} \):
for logits \( a_{ij} \) and values \( v_{ij\ell} \), with \( a'_{ij} = a_{i, d_j} \) and \( v'_{ij\ell} = v_{i, d_j, \ell} \),
\[
\operatorname{softmax}(a + ([j \in \operatorname{im} d] - 1)\infty)_i \, V_i \approx
\Bigl[ \sum_{j < m} \frac{e^{a'_{ij}}}{\sum_{k < m} e^{a'_{ik}}}\, v'_{ij\ell} \Bigr]_\ell .
\]
-/
@[main]
private lemma row
  {n m d : ℕ}
  {dm : Fin m → Fin n}
-- given
  (h : (Finset.univ.image dm).card = m)
  (h_m : 0 < m)
  (a : Fin n → Fin n → ℝ)
  (v : Fin n → Fin n → Fin d → ℝ)
  (a' : Fin n → Fin m → ℝ)
  (v' : Fin n → Fin m → Fin d → ℝ)
  (h_a : ∀ i j, a i (dm j) = a' i j)
  (h_v : ∀ i j l, v i (dm j) l = v' i j l)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide (j ∈ Finset.univ.image dm)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (a i j : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d] := [j < n] [l < d] (v i j l : Tensor ℝ [])
  ((A + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d]) ≈
    ((([l < d] ((∑ j, Real.exp (a' i j) / (∑ k, Real.exp (a' i k)) * v' i j l : ℝ) : Tensor ℝ [])) : Tensor ℝ [d]) : Tensor ℝ* [d]) := by
-- proof
  intro Ξ A Vᵢ
  have h0 := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Ite_Mul.row (fun i j => j ∈ Finset.univ.image dm) a
    (fun i j => Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => k ∈ Finset.univ.image dm), Real.exp (a i k)) v (ne_row h_m) (fun i j hp => rfl) i
  refine h0.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext l
  exact sc_ext (key h (a i) (a' i) (v i · l) (v' i · l) (h_a i) (fun j => h_v i j l))


/--
Matrix form of `row` when the values do not depend on the row:
\[
\operatorname{softmax}(a + ([j \in \operatorname{im} d] - 1)\infty)\, V \approx
\Bigl[ \sum_{j < m} \frac{e^{a_{i, d_j}}}{\sum_{k < m} e^{a_{i, d_k}}}\, V_{d_j \ell} \Bigr]_{i\ell} .
\]
-/
@[main]
private lemma main
  {n m d : ℕ}
  {dm : Fin m → Fin n}
-- given
  (h : (Finset.univ.image dm).card = m)
  (h_m : 0 < m)
  (a : Fin n → Fin n → ℝ)
  (v : Fin n → Fin d → ℝ) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [_i < n] [j < n] (Bool.toNat (decide (j ∈ Finset.univ.image dm)))
  let A : Tensor ℝ* [n, n] := ([i < n] [j < n] (a i j : Tensor ℝ []) : Tensor ℝ [n, n])
  let V : Tensor ℝ [n, d] := [j < n] [l < d] (v j l : Tensor ℝ [])
  (A + (Ξ - 1) * ∞).softmax @ (V : Tensor ℝ* [n, d]) ≈
    ((([i < n] [l < d] ((∑ j, Real.exp (a i (dm j)) / (∑ k, Real.exp (a i (dm k))) * v (dm j) l : ℝ) : Tensor ℝ [])) : Tensor ℝ [n, d]) : Tensor ℝ* [n, d]) := by
-- proof
  intro Ξ A V
  have h0 := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Ite_Mul (fun i j => j ∈ Finset.univ.image dm) a
    (fun i j => Real.exp (a i j) / ∑ k ∈ Finset.univ.filter (fun k => k ∈ Finset.univ.image dm), Real.exp (a i k)) v (ne_row h_m) (fun i j hp => rfl)
  refine h0.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext i
  congr 1
  funext l
  exact sc_ext (key h (a i) (fun j => a i (dm j)) (v · l) (fun j => v (dm j) l) (fun j => rfl) (fun j => rfl))


-- created on 2026-10-01