import sympy.Basic
import sympy.concrete.expr_with_limits
import sympy.tensor.lstm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Intervals


@[main]
private lemma adam
  {β : ℝ}
  {m g : ℕ → ℝ}
  {k : ℕ}
-- given
  (h₀ : m 0 = 0)
  (h₁ : ∀ t > 0, m t = β * m (t - 1) + (1 - β) * g t)
  (h₂ : β ≠ 0) :
-- imply
  m k = β ^ k * (1 - β) * ∑ t ∈ Finset.Icc 1 k, (β ^ t)⁻¹ * g t := by
-- proof
  induction k with
  | zero =>
    simp [h₀]
  | succ k ih =>
    rw [h₁ (k + 1) (by omega), Nat.add_sub_cancel, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    field_simp
    ring


@[main]
private lemma exponential_moving_average
  {β : ℝ}
  {v θ : ℕ → ℝ}
  {n : ℕ}
-- given
  (h₀ : v 0 = 0)
  (h₁ : ∀ t > 0, v t = β * v (t - 1) + (1 - β) * θ t) :
-- imply
  v n = θ 0 * (1 - β ^ n) + ∑ t ∈ Finset.range n, (1 - β ^ (n - t)) * (θ (t + 1) - θ t) := by
-- proof
  have key : ∀ n, v n = θ n - θ 0 * β ^ n - ∑ t ∈ Finset.range n, β ^ (n - t) * (θ (t + 1) - θ t) := by
    intro n
    induction n with
    | zero =>
      simp [h₀]
    | succ n ih =>
      have hs : ∑ t ∈ Finset.range n, β ^ (n + 1 - t) * (θ (t + 1) - θ t) = β * ∑ t ∈ Finset.range n, β ^ (n - t) * (θ (t + 1) - θ t) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t ht => ?_
        have ht := Finset.mem_range.mp ht
        rw [show n + 1 - t = n - t + 1 by omega, pow_succ]
        ring
      rw [h₁ (n + 1) (by omega), Nat.add_sub_cancel, ih, Finset.sum_range_succ, hs, show n + 1 - n = 1 by omega]
      ring
  have hd : ∑ t ∈ Finset.range n, (1 - β ^ (n - t)) * (θ (t + 1) - θ t) = ∑ t ∈ Finset.range n, (θ (t + 1) - θ t) - ∑ t ∈ Finset.range n, β ^ (n - t) * (θ (t + 1) - θ t) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [key n, hd, Finset.sum_range_sub θ n]
  ring


@[main]
private lemma fastformer
  {n d : ℕ}
  {w : Fin d → ℝ}
  {K' V V' : Fin n → Fin d → ℝ}
  {i : Fin n}
  {j : Fin d}
-- given
  (h : ∀ i j, V' i j = (∑ r, Real.exp ((∑ c, K' r c * w c) / Real.sqrt d) / (∑ q, Real.exp ((∑ c, K' q c * w c) / Real.sqrt d)) * K' r j) * V i j) :
-- imply
  V' i j = V i j * (∑ r, K' r j * Real.exp ((∑ c, K' r c * w c) / Real.sqrt d)) / ∑ q, Real.exp ((∑ c, K' q c * w c) / Real.sqrt d) := by
-- proof
  rw [h, mul_comm, mul_div_assoc, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  ring


@[main]
private lemma long_short_term_memory
  {dx dh : ℕ}
  {W : Matrix (Fin dx) (Fin 4 × Fin dh) ℝ}
  {Wh : Matrix (Fin dh) (Fin 4 × Fin dh) ℝ}
  {b : Fin 4 × Fin dh → ℝ}
  {x : ℕ → Fin dx → ℝ}
  {h c : ℕ → Fin dh → ℝ}
-- given
  (h₀ : ∀ t, h t = (lstm W Wh b x t).1)
  (h₁ : ∀ t, c t = (lstm W Wh b x t).2)
  {t : ℕ}
  (ht : 0 < t) :
-- imply
  h t = fun u => sigmoid (lstmGate W Wh b 3 (x t) (h (t - 1)) u) *
    Real.tanh (sigmoid (lstmGate W Wh b 1 (x t) (h (t - 1)) u) * c (t - 1) u +
      sigmoid (lstmGate W Wh b 0 (x t) (h (t - 1)) u) * Real.tanh (lstmGate W Wh b 2 (x t) (h (t - 1)) u)) := by
-- proof
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, h₀ (s + 1), h₀ s, h₁ s]
  rfl


@[main]
private lemma kmeans.nonoverlapping
  {M k d : ℕ} [NeZero k]
  {w w' : Fin k → Finset ℕ}
  {x : ℕ → EuclideanSpace ℝ (Fin d)}
-- given
  (_h₀ : ∑ i, (w i).card = M)
  (_h₁ : Finset.univ.biUnion w = Finset.range M)
  (h₂ : ∀ i, w' i = (Finset.range M).filter fun j =>
    ArgMin Set.univ (fun i' => ‖x j - ((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j'‖) = i) :
-- imply
  ∑ i, (w' i).card = M ∧ Finset.univ.biUnion w' = Finset.range M := by
-- proof
  obtain ⟨a, ha⟩ : ∃ a : ℕ → Fin k, ∀ j, ArgMin Set.univ (fun i' => ‖x j - ((w i').card : ℝ)⁻¹ • ∑ j' ∈ w i', x j'‖) = a j :=
    ⟨_, fun _ => rfl⟩
  simp only [ha] at h₂
  constructor
  · simp only [h₂]
    rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (a j)), Finset.card_range]
  · ext j
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, h₂, Finset.mem_filter]
    constructor
    · rintro ⟨i, hj, _⟩
      exact hj
    · intro hj
      exact ⟨a j, hj, rfl⟩


-- created on 2020-12-22
