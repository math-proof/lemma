import Mathlib
import sympy.Basic
import Def.v1.Atlas.BooleanFunctions.code.Claim21Lec10
open Finset BigOperators Real Filter BooleanFourier


namespace BooleanFourier

/--
[majorityFn_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim21Lec10.lean)
-/
@[path]
lemma majorityFn_compl
  {n : ℕ}
  {x : Fin n → Bool}
-- given
  (hn : Odd n) :
-- imply
  majorityFn n (fun i => !(x i)) = -(majorityFn n x) := by
-- proof
  classical
  simp only [majorityFn]
  set k := (univ.filter (fun i : Fin n => x i = true)).card
  have hk_le : k ≤ n := (Finset.card_filter_le _ _).trans (by simp [Finset.card_univ, Fintype.card_fin])
  have hcard : (univ.filter (fun i : Fin n => !(x i) = true)).card = n - k := by
    have heq : (univ.filter (fun i : Fin n => !(x i) = true)).card =
      (univ.filter (fun i : Fin n => x i = false)).card := by
      congr 1; ext i; simp
    rw [heq]
    have hcomp : (univ.filter (fun i : Fin n => x i = false)).card +
      (univ.filter (fun i : Fin n => x i = true)).card =
      (univ : Finset (Fin n)).card := by
      rw [← Finset.card_union_of_disjoint (by
        apply Finset.disjoint_filter.mpr
        intro i _ h1 h2; cases (x i) <;> simp_all)]
      congr 1
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases (x i) <;> simp
    simp [Finset.card_univ, Fintype.card_fin] at hcomp
    omega
  have hsimp : (univ.filter (fun i : Fin n => (fun i => !(x i)) i = true)).card = n - k := by
    convert hcard using 2; ext i; simp
  conv_lhs => rw [hsimp]
  obtain ⟨m, hm⟩ := hn
  split_ifs with h1 h2 <;> try ring <;> omega

end BooleanFourier

namespace BooleanFourier

/--
[chi_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim21Lec10.lean)
-/
@[path]
lemma chi_compl
  {n : ℕ}
  {S : Finset (Fin n)}
  {x : Fin n → Bool} :
-- imply
  chi S (fun i => !(x i)) = (-1) ^ S.card * chi S x := by
-- proof
  simp only [chi]
  rw [show ∏ i ∈ S, boolToReal ((fun i => !(x i)) i) = ∏ i ∈ S, boolToReal (!(x i)) from rfl]
  rw [show ∏ i ∈ S, boolToReal (!(x i)) = ∏ i ∈ S, ((-1) * boolToReal (x i)) from by
    congr 1; ext i; cases (x i) <;> simp [boolToReal]]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

end BooleanFourier

namespace BooleanFourier

/--
[fourierCoeff_majorityFn_even_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim21Lec10.lean)
-/
@[path]
lemma fourierCoeff_majorityFn_even_eq_zero
  {n : ℕ}
  {S : Finset (Fin n)}
-- given
  (hn : Odd n)
  (hS : Even S.card) :
-- imply
  fourierCoeff (majorityFn n) S = 0 := by
-- proof
  classical
  simp only [fourierCoeff]
  suffices h : ∑ x : Fin n → Bool, majorityFn n x * chi S x = 0 by
    rw [h, mul_zero]
  apply Finset.sum_involution (fun x _ => fun i => !(x i))
  · intro x _
    rw [majorityFn_compl hn x, chi_compl S x, hS.neg_one_pow, one_mul]; ring
  · intro x _ hne
    intro heq
    have h0 : ∀ i, x i = !(x i) := fun i => congr_fun heq.symm i
    exact absurd (h0 ⟨0, by obtain ⟨m, hm⟩ := hn; omega⟩) (by cases (x ⟨0, _⟩) <;> simp)
  · intro x _; exact Finset.mem_univ _
  · intro x _; funext i; simp

end BooleanFourier


-- created on 2026-10-23
