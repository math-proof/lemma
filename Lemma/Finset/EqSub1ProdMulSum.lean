import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma iterate_mul
  [CommRing R]
  (s : RingHom R R)
  (n : ℕ)
  (a b : R) :
  -- imply
  Nat.iterate (⇑s) n (a * b) = Nat.iterate (⇑s) n a * Nat.iterate (⇑s) n b := by
  -- proof
  rw [← RingHom.coe_pow, map_mul]

private lemma iterate_add
  [CommRing R]
  (s : RingHom R R)
  (n : ℕ)
  (a b : R) :
  -- imply
  Nat.iterate (⇑s) n (a + b) = Nat.iterate (⇑s) n a + Nat.iterate (⇑s) n b := by
  -- proof
  rw [← RingHom.coe_pow, map_add]

private lemma iterate_eq
  [CommRing R]
  (s : RingHom R R)
  (x lam u : R)
  (n : ℕ)
  -- given
  (h : s x = lam * x + u) :
  -- imply
  Nat.iterate (⇑s) n x = (∏ i ∈ Finset.range n, Nat.iterate (⇑s) i lam) * x +
    ∑ j ∈ Finset.range n, (∏ i ∈ Finset.Ico (j + 1) n, Nat.iterate (⇑s) i lam) * Nat.iterate (⇑s) j u := by
  -- proof
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ∑ j ∈ Finset.range n, Nat.iterate (⇑s) n lam *
        ((∏ i ∈ Finset.Ico (j + 1) n, Nat.iterate (⇑s) i lam) * Nat.iterate (⇑s) j u) =
      ∑ j ∈ Finset.range n, (∏ i ∈ Finset.Ico (j + 1) (n + 1), Nat.iterate (⇑s) i lam) *
        Nat.iterate (⇑s) j u := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j + 1 ≤ n := Finset.mem_range.mp hj
      rw [Finset.prod_Ico_succ_top hj']
      ring
    rw [Function.iterate_succ_apply, h, iterate_add, iterate_mul, ih, Finset.prod_range_succ,
      Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty, one_mul, mul_add, Finset.mul_sum, key]
    ring

/--
[RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_one_sub_prod_iterate_mul_eq_sum_prod_iterate_mul_iterate_of_apply_eq_mul_add.lean)
-/
@[path]
private lemma main
  [CommRing R]
  (s : RingHom R R)
  (ℓ : ℕ)
  (x lam u : R)
  -- given
  (hs : ∀ r : R, Nat.iterate (⇑s) ℓ r = r)
  (h : s x = lam * x + u) :
  -- imply
  (1 - ∏ i ∈ Finset.range ℓ, Nat.iterate (⇑s) i lam) * x =
    ∑ j ∈ Finset.range ℓ, (∏ i ∈ Finset.Ico (j + 1) ℓ, Nat.iterate (⇑s) i lam) * Nat.iterate (⇑s) j u := by
  -- proof
  have key := iterate_eq s x lam u ℓ h
  rw [hs] at key
  linear_combination key


-- created on 2026-10-20
