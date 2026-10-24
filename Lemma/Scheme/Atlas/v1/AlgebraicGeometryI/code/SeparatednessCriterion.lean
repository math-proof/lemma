import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SeparatednessCriterion
open Nat MvPolynomial


/--
[card_antidiagonalTuple](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean)
-/
@[path]
lemma card_antidiagonalTuple
  {k n : ℕ} :
-- imply
  (Finset.Nat.antidiagonalTuple k n).card = Nat.multichoose k n := by
-- proof
  change (List.Nat.antidiagonalTuple k n).length = Nat.multichoose k n
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [List.Nat.antidiagonalTuple_zero_zero]
    | succ n => simp [List.Nat.antidiagonalTuple_zero_succ]
  | succ k ih =>
    show (List.Nat.antidiagonalTuple (k + 1) n).length = _
    unfold List.Nat.antidiagonalTuple
    rw [List.length_flatMap]
    simp only [List.length_map, ih]
    show (List.map (fun a => k.multichoose a.2)
      (List.map (fun i => (i, n - i)) (List.range (n + 1)))).sum = _
    rw [List.map_map]
    simp only [Function.comp_def]
    have h1 : (List.map (fun i => Nat.multichoose k (n - i)) (List.range (n + 1))).sum =
      ∑ i ∈ Finset.range (n + 1), Nat.multichoose k (n - i) := by
      show _ = (Finset.range (n + 1)).sum _
      rw [Finset.sum, show (Finset.range (n + 1)).val = ↑(List.range (n + 1)) from rfl,
        Multiset.map_coe, Multiset.sum_coe]
    rw [h1, Finset.sum_flip, Nat.sum_range_multichoose, Nat.multichoose_eq,
      show k + 1 + n - 1 = n + k from by omega, Nat.choose_symm_add]

/--
[Nat.card_antidiagonal_tuple_choose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean)
-/
@[path]
lemma Nat.card_antidiagonal_tuple_choose
  {n d : ℕ} :
-- imply
  (Finset.Nat.antidiagonalTuple (n + 1) d).card = Nat.choose (n + d) d := by
-- proof
  rw [card_antidiagonalTuple, Nat.multichoose_eq,
    show n + 1 + d - 1 = n + d from by omega]

/--
[pow_le_ascFactorial_succ'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean)
-/
@[path]
lemma pow_le_ascFactorial_succ'
  {n d : ℕ} :
-- imply
  n ^ d ≤ (n + 1).ascFactorial d := by
-- proof
  induction d with
  | zero => simp [Nat.ascFactorial]
  | succ d ih =>
    rw [pow_succ]
    calc n ^ d * n
      ≤ (n + 1).ascFactorial d * n := Nat.mul_le_mul_right n ih
      _ ≤ (n + 1).ascFactorial d * (n + 1 + d) := Nat.mul_le_mul_left _ (by omega)
      _ = (n + 1 + d) * (n + 1).ascFactorial d := by ring

/--
[growthFun_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean)
-/
@[path]
lemma growthFun_lower_bound
  {n d : ℕ} :
-- imply
  n ^ d ≤ d.factorial * growthFun_polyring d n := by
-- proof
  simp only [growthFun_polyring]
  calc n ^ d ≤ (n + 1).ascFactorial d := pow_le_ascFactorial_succ' n d
    _ = d.factorial * (n + d).choose d := Nat.ascFactorial_eq_factorial_mul_choose n d

/--
[growthFun_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean)
-/
@[path]
lemma growthFun_upper_bound
  {n d : ℕ}
-- given
  (hnd : d ≤ n) :
-- imply
  growthFun_polyring d n ≤ 2 ^ d * n ^ d := by
-- proof
  simp only [growthFun_polyring]
  calc (n + d).choose d ≤ (n + d) ^ d := Nat.choose_le_pow _ _
    _ ≤ (2 * n) ^ d := by apply Nat.pow_le_pow_left; omega
    _ = 2 ^ d * n ^ d := by ring

/--
[proposition_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean)
-/
@[path]
lemma proposition_11
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [Algebra k A]
  [Algebra.FiniteType k A]
  {d : ℕ}
  {m : ℕ}
  {f : MvPolynomial (Fin m) k →ₐ[k] A}
-- given
  (hd : ringKrullDim A = d)
  (hf : Function.Surjective f) :
-- imply
  ∃ (c' c : ℕ), 0 < c' ∧ 0 < c ∧ (∀ n : ℕ, n ^ d ≤ c' * growthFun f n) ∧ (∀ n : ℕ, d ≤ n → growthFun f n ≤ c * n ^ d) := by
-- proof
  obtain ⟨C, hC_pos, hle, hup⟩ := noether_normalization_growth_comparison' k A d hd m f hf
  refine ⟨d.factorial, C * 2 ^ d, Nat.factorial_pos d, by positivity, ?_, ?_⟩
  · intro n
    calc n ^ d ≤ d.factorial * growthFun_polyring d n := growthFun_lower_bound n d
      _ ≤ d.factorial * growthFun f n := Nat.mul_le_mul_left _ (hle n)
  · intro n hnd
    calc growthFun f n ≤ C * growthFun_polyring d n := hup n
      _ ≤ C * (2 ^ d * n ^ d) :=
        Nat.mul_le_mul_left C (growthFun_upper_bound n d hnd)
      _ = (C * 2 ^ d) * n ^ d := by ring


-- created on 2026-10-23
