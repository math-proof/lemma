import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Intervals
import sympy.Basic
open Matrix


@[path]
private lemma index_general.swap
  {n : ℕ}
  {x : Fin n → ℕ}
  {i j : ℕ}
  {p q : Fin n}
-- given
  (h : Finset.univ.image x = Finset.range n)
  (hi : i < n)
  (hj : j < n)
  (hp : (p : ℕ) = ∑ k, (if x k = i then 1 else 0) * (k : ℕ))
  (hq : (q : ℕ) = ∑ k, (if x k = j then 1 else 0) * (k : ℕ)) :
-- imply
  ∑ k, (if ((Matrix.of fun a b : Fin n => if b = Equiv.swap p q a then (1 : ℕ) else 0) *ᵥ x) k = i then 1 else 0) * (k : ℕ) = ∑ k, (if x k = j then 1 else 0) * (k : ℕ) := by
-- proof
  have hinj : Function.Injective x := by
    have hc : (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card := by
      rw [h, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact fun a b hab => (Finset.card_image_iff.mp hc) (by simp) (by simp) hab
  have hsurj : ∀ v < n, ∃ a, x a = v := fun v hv => by
    have : v ∈ Finset.univ.image x := by
      rw [h]
      exact Finset.mem_range.mpr hv
    simpa using this
  have hidx : ∀ (y : Fin n → ℕ) (a : Fin n) (v : ℕ), y a = v → Function.Injective y →
      (∑ k, (if y k = v then 1 else 0) * (k : ℕ)) = a := by
    intro y a v ha hy
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [if_neg (fun e => hb (hy (e.trans ha.symm))), zero_mul]
    · simp
  obtain ⟨p0, hp0⟩ := hsurj i hi
  obtain ⟨q0, hq0⟩ := hsurj j hj
  have hp' : p = p0 := Fin.ext (by rw [hp, hidx x p0 i hp0 hinj])
  have hq' : q = q0 := Fin.ext (by rw [hq, hidx x q0 j hq0 hinj])
  subst hp' hq'
  have hy : ((Matrix.of fun a b : Fin n => if b = Equiv.swap p q a then (1 : ℕ) else 0) *ᵥ x) = fun a => x (Equiv.swap p q a) := by
    funext a
    simp [Matrix.mulVec, dotProduct]
  rw [hy, hidx x q j hq0 hinj]
  exact hidx _ q i (by simp [hp0]) (hinj.comp (Equiv.injective _))


@[path]
private lemma index.swap
  {n : ℕ}
  {x : Fin n → ℕ}
  {i j : ℕ}
  {p q : Fin n}
-- given
  (h : Finset.univ.image x = Finset.range n)
  (hi : i < n)
  (hj : j < n)
  (hp : (p : ℕ) = ∑ k, (if x k = i then 1 else 0) * (k : ℕ))
  (hq : (q : ℕ) = ∑ k, (if x k = j then 1 else 0) * (k : ℕ)) :
-- imply
  ∑ k, (if ((Matrix.of fun a b : Fin n => if b = Equiv.swap p q a then (1 : ℕ) else 0) *ᵥ x) k = i then 1 else 0) * (k : ℕ) = ∑ k, (if x k = j then 1 else 0) * (k : ℕ) := by
-- proof
  have hinj : Function.Injective x := by
    have hc : (Finset.univ.image x).card = (Finset.univ : Finset (Fin n)).card := by
      rw [h, Finset.card_range, Finset.card_univ, Fintype.card_fin]
    exact fun a b hab => (Finset.card_image_iff.mp hc) (by simp) (by simp) hab
  have hsurj : ∀ v < n, ∃ a, x a = v := fun v hv => by
    have : v ∈ Finset.univ.image x := by
      rw [h]
      exact Finset.mem_range.mpr hv
    simpa using this
  have hidx : ∀ (y : Fin n → ℕ) (a : Fin n) (v : ℕ), y a = v → Function.Injective y →
      (∑ k, (if y k = v then 1 else 0) * (k : ℕ)) = a := by
    intro y a v ha hy
    rw [Finset.sum_eq_single a]
    · simp [ha]
    · intro b _ hb
      rw [if_neg (fun e => hb (hy (e.trans ha.symm))), zero_mul]
    · simp
  obtain ⟨p0, hp0⟩ := hsurj i hi
  obtain ⟨q0, hq0⟩ := hsurj j hj
  have hp' : p = p0 := Fin.ext (by rw [hp, hidx x p0 i hp0 hinj])
  have hq' : q = q0 := Fin.ext (by rw [hq, hidx x q0 j hq0 hinj])
  subst hp' hq'
  have hy : ((Matrix.of fun a b : Fin n => if b = Equiv.swap p q a then (1 : ℕ) else 0) *ᵥ x) = fun a => x (Equiv.swap p q a) := by
    funext a
    simp [Matrix.mulVec, dotProduct]
  rw [hy, hidx x q j hq0 hinj]
  exact hidx _ q i (by simp [hp0]) (hinj.comp (Equiv.injective _))


@[path]
private lemma rsolve
  {x f : ℕ → ℝ}
  {c : ℝ}
-- given
  (_h₀ : c ≠ 0)
  (h : ∀ n, x (n + 1) = c * x n + f n) :
-- imply
  ∀ n, x n = x 0 * c ^ n + ∑ k ∈ Finset.range n, f k * c ^ (n - k - 1) := by
-- proof
  have hstep : ∀ n, ∑ k ∈ Finset.range (n + 1), f k * c ^ (n + 1 - k - 1) = c * ∑ k ∈ Finset.range n, f k * c ^ (n - k - 1) + f n := by
    intro n
    rw [Finset.sum_range_succ, Finset.mul_sum, show n + 1 - n - 1 = 0 by omega, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k - 1 = (n - k - 1) + 1 by omega, pow_succ]
    ring
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [h, ih, hstep]
    ring


@[path]
private lemma swap2.general
  {α : Type*}
  {n : ℕ}
  {s : Set (Fin (n + 1) → α)}
-- given
  (h : ∀ j : Fin (n + 1), 0 < j → ∀ x ∈ s, (fun a => if a = j then x 0 else if a = 0 then x j else x a) ∈ s) :
-- imply
  ∀ i j : Fin (n + 1), ∀ x ∈ s, (fun a => x (Equiv.swap i j a)) ∈ s := by
-- proof
  have T : ∀ j : Fin (n + 1), ∀ x ∈ s, (fun a => x (Equiv.swap 0 j a)) ∈ s := by
    intro j x hx
    by_cases hj : j = 0
    · subst hj
      simpa using hx
    · have := h j (Fin.pos_iff_ne_zero.mpr hj) x hx
      convert this using 1
      funext a
      rw [Equiv.swap_apply_def]
      by_cases h1 : a = 0 <;> by_cases h2 : a = j <;> simp_all
  intro i j x hx
  by_cases hij : i = j
  · subst hij
    simpa using hx
  by_cases hi0 : i = 0
  · subst hi0
    exact T j x hx
  by_cases hj0 : j = 0
  · subst hj0
    rw [Equiv.swap_comm]
    exact T i x hx
  rw [← Equiv.swap_mul_swap_mul_swap hj0 (Ne.symm hij), Equiv.swap_comm j 0]
  exact T i _ (T j _ (T i x hx))


@[path]
private lemma bilinear.symm
  {n : ℕ}
  {W : Matrix (Fin n) (Fin n) ℝ}
-- given
  (h : W = Wᵀ)
  (x y : Fin n → ℝ) :
-- imply
  x ⬝ᵥ (W *ᵥ y) = y ⬝ᵥ (W *ᵥ x) := by
-- proof
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← h, dotProduct_comm]


-- created on 2023-06-17
