import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band
import sympy.Basic
open Tensor
set_option maxHeartbeats 2000000


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]


@[main]
private lemma position_representation.relative.band_part_mask.indexed
  {n d_z : ℕ}
  {l u : ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {K'' V'' : Fin n → ℕ → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
  {r : Fin n → ℤ}
-- given
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min (r j - r i) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min (r j - r i) c)) t)
  (h₂ : ∀ (i : Fin n) (j : ℕ) t, K'' i j t = wK (c + max (-c) (min (r ⟨min (n - 1) (j + (i.val + 1 - l)), by have := i.2; omega⟩ - r i) c)) t)
  (h₃ : ∀ (i : Fin n) (j : ℕ) t, V'' i j t = wV (c + max (-c) (min (r ⟨min (n - 1) (j + (i.val + 1 - l)), by have := i.2; omega⟩ - r i) c)) t)
  (h_l : 0 < l)
  (h_u : 0 < u)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] ((((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ)) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [s < d_z] ((V j s + V' i j s : ℝ) : Tensor ℝ [])
  ((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([s < d_z] ((∑ j' : Fin (min n (i.val + u) - (i.val + 1 - l)), Real.exp ((∑ t, Q i t * (K ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ t + K'' i j' t)) / √(d_z : ℝ)) / (∑ k' : Fin (min n (i.val + u) - (i.val + 1 - l)), Real.exp ((∑ t, Q i t * (K ⟨i.val + 1 - l + k', by have := k'.2; omega⟩ t + K'' i k' t)) / √(d_z : ℝ))) * (V ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ s + V'' i j' s) : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  intro Ξ A₀ Vᵢ
  have h_main := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band.window h_l h_u (fun i j => ((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ))) (fun i j s => V j s + V' i j s) i
  refine h_main.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext s
  apply sc_ext
  have e : ∀ j' : Fin (min n (i.val + u) - (i.val + 1 - l)), ((⟨min (n - 1) (j'.val + (i.val + 1 - l)), by have := i.2; omega⟩ : Fin n)) = ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ :=
    fun j' => Fin.ext (by have := j'.2; simp only; omega)
  simp only [h₀, h₁, h₂, h₃, e]


-- created on 2026-09-27
