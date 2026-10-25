import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ResidueSum
open Polynomial Finset BigOperators ResidueSum


namespace ResidueSum

/--
[prod_erase_eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma prod_erase_eval_zero
  [Field k]
  {n : ℕ}
  {a : Fin n → k}
  {i j : Fin n}
-- given
  (hij : i ≠ j) :
-- imply
  (∏ l ∈ Finset.univ.erase i, (X - C (a l))).eval (a j) = 0 := by
-- proof
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) (by simp)

end ResidueSum

namespace ResidueSum

/--
[coeff_summand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma coeff_summand
  [Field k]
  {n : ℕ}
  {c a : Fin n → k}
  {i : Fin n} :
-- imply
  (C (c i) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))).coeff (n - 1) = c i := by
-- proof
  rw [Polynomial.coeff_C_mul]
  have hm : (∏ j ∈ Finset.univ.erase i, (X - C (a j))).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun j _ => monic_X_sub_C (a j))
  have hd : (∏ j ∈ Finset.univ.erase i, (X - C (a j))).natDegree = n - 1 := by
    rw [Polynomial.natDegree_prod _ _ (fun j _ => (monic_X_sub_C (a j)).ne_zero)]
    simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  have : (∏ j ∈ Finset.univ.erase i, (X - C (a j))).coeff (n - 1) = 1 := by
    conv_lhs => rw [← hd]
    exact hm.leadingCoeff
  rw [this, mul_one]

end ResidueSum

namespace ResidueSum

/--
[residue_of_simple_pole](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_of_simple_pole
  [Field k]
  {c a : k} :
-- imply
  residueAtPole (C c) (X - C a) a = c := by
-- proof
  simp [residueAtPole, derivative_sub, derivative_X, derivative_C]

end ResidueSum

namespace ResidueSum

/--
[partialFracNumer_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma partialFracNumer_eval
  [Field k]
  {n : ℕ}
  {c a : Fin n → k}
  {j : Fin n} :
-- imply
  (partialFracNumer c a).eval (a j) = c j * ∏ l ∈ Finset.univ.erase j, (a j - a l) := by
-- proof
  unfold partialFracNumer
  simp only [eval_finset_sum, eval_mul, eval_C]
  rw [Finset.sum_eq_single j]
  · simp [eval_prod, eval_sub, eval_X, eval_C]
  · intro i _ hij
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    have : (∏ l ∈ Finset.univ.erase i, (a j - a l)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩) (by simp)
    rw [this]; ring
  · intro hj; exact absurd (Finset.mem_univ j) hj

end ResidueSum

namespace ResidueSum

/--
[poleProd_derivative_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma poleProd_derivative_eval
  [Field k]
  {n : ℕ}
  {a : Fin n → k}
  {j : Fin n} :
-- imply
  (poleProd a).derivative.eval (a j) = ∏ i ∈ Finset.univ.erase j, (a j - a i) := by
-- proof
  unfold poleProd
  rw [Polynomial.derivative_prod_finset]
  simp only [eval_finset_sum, derivative_sub, derivative_X, derivative_C, sub_zero, mul_one]
  rw [Finset.sum_eq_single j]
  · simp [eval_prod, eval_sub, eval_X, eval_C]
  · intro i _ hij
    have := prod_erase_eval_zero a i j hij
    simp [this]
  · intro hj; exact absurd (Finset.mem_univ j) hj

end ResidueSum

namespace ResidueSum

/--
[partialFracNumer_coeff_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma partialFracNumer_coeff_top
  [Field k]
  {n : ℕ}
  {c a : Fin n → k} :
-- imply
  (partialFracNumer c a).coeff (n - 1) = ∑ i, c i := by
-- proof
  unfold partialFracNumer
  simp only [Polynomial.finset_sum_coeff]
  exact Finset.sum_congr rfl (fun i _ => coeff_summand c a i)

end ResidueSum

namespace ResidueSum

/--
[derivative_at_simple_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma derivative_at_simple_root
  [Field k]
  {a : k}
  {R : k[X]} :
-- imply
  ((X - C a) * R).derivative.eval a = R.eval a := by
-- proof
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C]

end ResidueSum

namespace ResidueSum

/--
[residue_eq_eval_div_cofactor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_eq_eval_div_cofactor
  [Field k]
  {P R : k[X]}
  {a : k}
-- given
  (_hR : R.eval a ≠ 0) :
-- imply
  residueAtPole P ((X - C a) * R) a = P.eval a / R.eval a := by
-- proof
  unfold residueAtPole; rw [derivative_at_simple_root]

end ResidueSum

namespace ResidueSum

/--
[residue_partial_frac_eq_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_partial_frac_eq_coeff
  [Field k]
  {n : ℕ}
  {c a : Fin n → k}
  {j : Fin n}
-- given
  (hdist : Function.Injective a) :
-- imply
  residuePartialFrac c a j = c j := by
-- proof
  unfold residuePartialFrac residueAtPole
  rw [partialFracNumer_eval, poleProd_derivative_eval]
  have hprod : ∏ l ∈ Finset.univ.erase j, (a j - a l) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi; rw [Finset.mem_erase] at hi
    exact sub_ne_zero.mpr (fun h => hi.1 (hdist h.symm))
  field_simp

end ResidueSum

namespace ResidueSum

/--
[residueAtInf_eq_neg_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residueAtInf_eq_neg_sum
  [Field k]
  {n : ℕ}
  {c a : Fin n → k} :
-- imply
  residueAtInfPartialFrac c a = -(∑ i, c i) := by
-- proof
  unfold residueAtInfPartialFrac; rw [partialFracNumer_coeff_top]

end ResidueSum

namespace ResidueSum

/--
[residue_sum_partial_frac](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_sum_partial_frac
  [Field k]
  {n : ℕ}
  {c : Fin n → k}
  {a : Fin n → k}
-- given
  (hdist : Function.Injective a) :
-- imply
  (∑ i, residuePartialFrac c a i) + residueAtInfPartialFrac c a = 0 := by
-- proof
  have h1 : ∀ i, residuePartialFrac c a i = c i :=
    fun i => residue_partial_frac_eq_coeff c a i hdist
  simp_rw [h1, residueAtInf_eq_neg_sum, add_neg_cancel]

end ResidueSum

namespace ResidueSum

/--
[residue_sum_const_over_two_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_sum_const_over_two_linear
  [Field k]
  {a b c : k}
-- given
  (hab : a ≠ b) :
-- imply
  residueAtPole (C c) ((X - C a) * (X - C b)) a + residueAtPole (C c) ((X - C a) * (X - C b)) b = 0 := by
-- proof
  simp only [residueAtPole, eval_C]
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C]
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp; ring

end ResidueSum

namespace ResidueSum

/--
[residue_sum_poly_two_poles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_sum_poly_two_poles
  [Field k]
  {P : k[X]}
  {a b : k}
-- given
  (hab : a ≠ b)
  (hP : P.natDegree ≤ 1) :
-- imply
  residueAtPole P ((X - C a) * (X - C b)) a + residueAtPole P ((X - C a) * (X - C b)) b + (-P.coeff 1) = 0 := by
-- proof
  simp only [residueAtPole]
  simp [derivative_mul, derivative_sub, derivative_X, derivative_C]
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hP_eq : P = C (P.coeff 0) + C (P.coeff 1) * X := by
    ext n; simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X]
    match n with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      have : P.coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  rw [hP_eq]; simp [eval_add, eval_mul, eval_C, eval_X]; field_simp; ring

end ResidueSum

namespace ResidueSum

/--
[residue_sum_linear_over_two_poles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_sum_linear_over_two_poles
  [Field k]
  {a b d e : k}
-- given
  (hab : a ≠ b) :
-- imply
  (d * a + e) / (a - b) + (d * b + e) / (b - a) + (-d) = 0 := by
-- proof
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hab
  have h2 : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  field_simp; ring

end ResidueSum

namespace ResidueSum

/--
[residue_sum_logarithmic_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ResidueSum.lean)
-/
@[path]
lemma residue_sum_logarithmic_form
  [Field k]
  {n m : ℕ}
  {_zeros : Fin n → k}
  {_poles : Fin m → k} :
-- imply
  (∑ _i : Fin n, (1 : k)) + (∑ _j : Fin m, (-1 : k)) + ((↑m : k) - (↑n : k)) = 0 := by
-- proof
  simp [Finset.sum_const]; ring

end ResidueSum


-- created on 2026-10-23
