import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StirlingMatrices
open BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[Ssv_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma Ssv_eq_zero_of_lt (n k : ℕ) (h : n < k) : Ssv n k = 0 := by
  unfold Ssv
  rw [Nat.stirlingSecond_eq_zero_of_lt h, Nat.cast_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Ssv_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma Ssv_zero_zero : Ssv 0 0 = 1 := by
  unfold Ssv
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Ssv_zero_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma Ssv_zero_succ (m : ℕ) : Ssv 0 (m + 1) = 0 := by
  unfold Ssv
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Ssv_succ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma Ssv_succ_zero (n : ℕ) : Ssv (n + 1) 0 = 0 := by
  unfold Ssv
  rw [Nat.stirlingSecond_succ_zero, Nat.cast_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Ssv_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma Ssv_succ_succ (k m : ℕ) :
  Ssv (k + 1) (m + 1) = (m + 1) * Ssv k (m + 1) + Ssv k m := by
  unfold Ssv
  rw [Nat.stirlingSecond_succ_succ]
  push_cast
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[key](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma key : ∀ n m, (∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k * Ssv k m)
  = if n = m then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro m
    simp only [Nat.zero_add, Finset.sum_range_one]
    rw [signedStirlingFirst_self, one_mul]
    cases m with
    | zero => simp [Ssv_zero_zero]
    | succ m =>
      simp [Ssv_zero_succ]
  | succ n ih =>
    intro m
    cases m with
    | zero =>
      have hne : ¬ (n + 1 = 0) := by omega
      simp only [hne, ite_false]
      apply Finset.sum_eq_zero
      intro k hk
      cases k with
      | zero => simp [signedStirlingFirst_succ_zero]
      | succ k => simp [Ssv_succ_zero]
    | succ m =>
      have h0 : signedStirlingFirst (n + 1) 0 * Ssv 0 (m + 1) = 0 := by
        rw [signedStirlingFirst_succ_zero, zero_mul]
      have expand : ∀ k, signedStirlingFirst (n + 1) (k + 1) * Ssv (k + 1) (m + 1) =
        ((m + 1) : ℤ) * (signedStirlingFirst n k * Ssv k (m + 1))
          + (signedStirlingFirst n k * Ssv k m)
          - n * (signedStirlingFirst n (k + 1) * Ssv (k + 1) (m + 1)) := by
        intro k
        rw [signedStirlingFirst_succ_succ, Ssv_succ_succ]
        ring
      have hC : (∑ k ∈ Finset.range (n + 1), signedStirlingFirst n (k + 1) * Ssv (k + 1) (m + 1))
        = ∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k * Ssv k (m + 1) := by
        have e1' : (∑ k ∈ Finset.range (n + 1 + 1), signedStirlingFirst n k * Ssv k (m + 1))
          = (∑ k ∈ Finset.range (n + 1), signedStirlingFirst n (k + 1) * Ssv (k + 1) (m + 1))
          + signedStirlingFirst n 0 * Ssv 0 (m + 1) :=
          Finset.sum_range_succ' _ _
        have e2' : (∑ k ∈ Finset.range (n + 1 + 1), signedStirlingFirst n k * Ssv k (m + 1))
          = (∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k * Ssv k (m + 1))
          + signedStirlingFirst n (n + 1) * Ssv (n + 1) (m + 1) :=
          Finset.sum_range_succ _ _
        have g0 : signedStirlingFirst n 0 * Ssv 0 (m + 1) = 0 := by
          cases n with
          | zero => rw [signedStirlingFirst_self, Ssv_zero_succ, one_mul]
          | succ n => rw [signedStirlingFirst_succ_zero, zero_mul]
        have gtop : signedStirlingFirst n (n + 1) * Ssv (n + 1) (m + 1) = 0 := by
          rw [signedStirlingFirst_eq_zero_of_lt (Nat.lt_succ_self _), zero_mul]
        have key2 :
          (∑ k ∈ Finset.range (n + 1), signedStirlingFirst n (k + 1) * Ssv (k + 1) (m + 1))
          + signedStirlingFirst n 0 * Ssv 0 (m + 1)
          = (∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k * Ssv k (m + 1))
          + signedStirlingFirst n (n + 1) * Ssv (n + 1) (m + 1) := by
          rw [← e1', ← e2']
        rwa [g0, gtop, add_zero, add_zero] at key2
      rw [Finset.sum_range_succ' _ (n + 1), h0, add_zero]
      change (∑ k ∈ Finset.range (n + 1), signedStirlingFirst (n + 1) (k + 1) * Ssv (k + 1) (m + 1))
        = (if n + 1 = m + 1 then (1 : ℤ) else 0)
      rw [Finset.sum_congr rfl (fun k _ => expand k),
        Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hC, ih m, ih (m + 1)]
      by_cases h1 : n = m
      · subst h1
        simp
      · by_cases h2 : n = m + 1
        · subst h2
          simp
        · simp [h1, h2]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_signedStirlingFirst_mul_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
lemma sum_signedStirlingFirst_mul_stirlingSecond
  {n m : ℕ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), signedStirlingFirst n k * (Nat.stirlingSecond k m : ℤ) =
    if n = m then 1 else 0 :=
-- proof
  key n m

end MetaMathlibExt

namespace MetaMathlibExt

/--
[smat_mul_Smat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma smat_mul_Smat (N : ℕ) : smat N * Smat N = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have hsum : (∑ k : Fin N, smat N i k * Smat N k j)
    = ∑ k ∈ Finset.range N, signedStirlingFirst i.1 k * Ssv k j.1 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => signedStirlingFirst i.1 k * Ssv k j.1) N]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rfl
  rw [hsum]
  have hsub : Finset.range (i.1 + 1) ⊆ Finset.range N := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hext : (∑ k ∈ Finset.range (i.1 + 1), signedStirlingFirst i.1 k * Ssv k j.1)
    = ∑ k ∈ Finset.range N, signedStirlingFirst i.1 k * Ssv k j.1 :=
    Finset.sum_subset hsub (fun x hxN hxNi => by
      have h1 : ¬ x < i.1 + 1 := fun h => hxNi (Finset.mem_range.mpr h)
      have h2 : i.1 < x := by omega
      change signedStirlingFirst i.1 x * Ssv x j.1 = 0
      rw [signedStirlingFirst_eq_zero_of_lt h2, zero_mul])
  rw [← hext, key i.1 j.1]
  by_cases h : i = j
  · subst h
    simp
  · have hne : i.1 ≠ j.1 := fun e => h (Fin.ext e)
    simp [hne, h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[smat_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma smat_lower (N : ℕ) (i j : Fin N) (h : i < j) : smat N i j = 0 := by
  change signedStirlingFirst i.1 j.1 = 0
  exact signedStirlingFirst_eq_zero_of_lt (Fin.lt_def.mp h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[Smat_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
private lemma Smat_lower (N : ℕ) (i j : Fin N) (h : i < j) : Smat N i j = 0 := by
  change Ssv i.1 j.1 = 0
  exact Ssv_eq_zero_of_lt _ _ (Fin.lt_def.mp h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[stirlingMatrices_mutualInverse_and_lowerTriangular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingMatrices.lean)
-/
@[path]
lemma stirlingMatrices_mutualInverse_and_lowerTriangular
  {N : ℕ} :
-- imply
  let s : Matrix (Fin N) (Fin N) ℤ := by
-- proof
  intro s S
  have es : s = smat N := rfl
  have eS : S = Smat N := rfl
  rw [es, eS]
  refine ⟨smat_mul_Smat N, mul_eq_one_comm.mp (smat_mul_Smat N), smat_lower N, Smat_lower N⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
