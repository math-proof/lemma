import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band
import sympy.Basic
open Tensor Hyperreal
set_option maxHeartbeats 2000000


private lemma sc_ext {x y : ℝ} (h : x = y) : (x : Tensor ℝ []) = (y : Tensor ℝ []) := by rw [h]


@[main]
private lemma main
  {n d_z : ℕ}
  {l u d : ℕ}
  {β : Fin n → ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {K'' V'' : Fin n → ℕ → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
  {r : Fin n → ℤ}
-- given
  (h_d : 0 < d)
  (h_dl : (d : ℤ) ∣ (l : ℤ) - 1)
  (h_β : ∀ i : Fin n, (β i : ℤ) = max ((i.val : ℤ) - l + 1) (((i.val : ℤ) - l + 1) % d))
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min (r j - r i) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min (r j - r i) c)) t)
  (h₂ : ∀ (i : Fin n) (j : ℕ) t, K'' i j t = wK (c + max (-c) (min (r ⟨min (n - 1) (j + β i), by have := i.2; omega⟩ - r i) c)) t)
  (h₃ : ∀ (i : Fin n) (j : ℕ) t, V'' i j t = wV (c + max (-c) (min (r ⟨min (n - 1) (j + β i), by have := i.2; omega⟩ - r i) c)) t)
  (h_l : 0 < l)
  (h_u : 0 < u)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] ((((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ)) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [s < d_z] ((V j s + V' i j s : ℝ) : Tensor ℝ [])
  ((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([s < d_z] ((∑ m : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ t, Q i t * (K ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ t + K'' i (m * d) t)) / √(d_z : ℝ)) / (∑ m' : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ t, Q i t * (K ⟨β i + m' * d, by have := Band.win_lt h_d m'.2; omega⟩ t + K'' i (m' * d) t)) / √(d_z : ℝ))) * (V ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ s + V'' i (m * d) s) : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  intro Ξ A₀ Vᵢ
  obtain ⟨hb1, hb2, hb3⟩ := Band.beta_props h_d h_dl (h_β i)
  have h_main := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band.dilated h_l h_u h_d (fun i j => ((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ))) (fun i j s => V j s + V' i j s) i hb1 hb2 hb3
  refine h_main.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext s
  apply sc_ext
  have e : ∀ m : Fin ((min n (i.val + u) - β i + d - 1) / d), ((⟨min (n - 1) (m.val * d + β i), by have := i.2; omega⟩ : Fin n)) = ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ :=
    fun m => Fin.ext (by have := Band.win_lt h_d m.2; simp only; omega)
  simp only [h₀, h₁, h₂, h₃, e]


@[main]
private lemma compact
  {n d_z : ℕ}
  {l u d : ℕ}
  {β : Fin n → ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {K'' V'' : Fin n → ℕ → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
  {r : Fin n → ℤ}
-- given
  (h_d : 0 < d)
  (h_dl : (d : ℤ) ∣ (l : ℤ) - 1)
  (h_β : ∀ i : Fin n, (β i : ℤ) = max ((i.val : ℤ) - l + 1) (((i.val : ℤ) - l + 1) % d))
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min (r j - r i) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min (r j - r i) c)) t)
  (h₂ : ∀ (i : Fin n) (m : ℕ) t, K'' i m t = wK (c + max (-c) (min (r ⟨min (n - 1) (d * m + β i), by have := i.2; omega⟩ - r i) c)) t)
  (h₃ : ∀ (i : Fin n) (m : ℕ) t, V'' i m t = wV (c + max (-c) (min (r ⟨min (n - 1) (d * m + β i), by have := i.2; omega⟩ - r i) c)) t)
  (h_l : 0 < l)
  (h_u : 0 < u)
  (i : Fin n) :
-- imply
  let Ξ : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (decide ((i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u ∧ ((j.val : ℤ) - (i.val : ℤ)) % d = 0)))
  let A₀ : Tensor ℝ* [n, n] := ([i < n] [j < n] ((((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ)) : ℝ) : Tensor ℝ []) : Tensor ℝ [n, n])
  let Vᵢ : Tensor ℝ [n, d_z] := [j < n] [s < d_z] ((V j s + V' i j s : ℝ) : Tensor ℝ [])
  ((A₀ + (Ξ - 1) * ∞).softmax.get ⟨i, by grind⟩) @ (Vᵢ : Tensor ℝ* [n, d_z]) ≈
    ((([s < d_z] ((∑ m : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ t, Q i t * (K ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ t + K'' i m t)) / √(d_z : ℝ)) / (∑ m' : Fin ((min n (i.val + u) - β i + d - 1) / d), Real.exp ((∑ t, Q i t * (K ⟨β i + m' * d, by have := Band.win_lt h_d m'.2; omega⟩ t + K'' i m' t)) / √(d_z : ℝ))) * (V ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ s + V'' i m s) : ℝ) : Tensor ℝ [])) : Tensor ℝ [d_z]) : Tensor ℝ* [d_z]) := by
-- proof
  intro Ξ A₀ Vᵢ
  obtain ⟨hb1, hb2, hb3⟩ := Band.beta_props h_d h_dl (h_β i)
  have h_main := DotSoftmaxAdd_Mul_Infty.eq.Cast_Stack_Sum_Band.dilated h_l h_u h_d (fun i j => ((∑ t, Q i t * (K j t + K' i j t)) / √(d_z : ℝ))) (fun i j s => V j s + V' i j s) i hb1 hb2 hb3
  refine h_main.trans (Tensor.XEq.of.Eq ?_)
  congr 1
  congr 1
  funext s
  apply sc_ext
  have e : ∀ m : Fin ((min n (i.val + u) - β i + d - 1) / d), ((⟨min (n - 1) (d * m.val + β i), by have := i.2; omega⟩ : Fin n)) = ⟨β i + m * d, by have := Band.win_lt h_d m.2; omega⟩ :=
    fun m => Fin.ext (by have := Band.win_lt h_d m.2; simp only [Nat.mul_comm d m.val]; omega)
  simp only [h₀, h₁, h₂, h₃, e]


-- created on 2021-12-27
