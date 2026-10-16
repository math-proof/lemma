import Mathlib
import sympy.Basic
open Polynomial IntermediateField


/--
[Algebra_norm_algebraMap_sub_eq_minpoly_eval](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_norm_algebraMap_sub_eq_minpoly_eval.lean)
-/
@[path]
private lemma main
  [Field F] [Field F'] [Algebra F F'] [Module.Finite F F']
  {x : F'}
-- given
  (hdeg : (minpoly F x).natDegree = Module.finrank F F')
  {c : F} :
-- imply
  Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
-- proof
  set y := x - algebraMap F F' c with hy
  have hyint : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  have hminy : minpoly F y = (minpoly F x).comp (X + C c) := minpoly.sub_algebraMap x c
  have hdegy : (minpoly F y).natDegree = Module.finrank F F' := by
    rw [hminy, natDegree_comp, natDegree_X_add_C, mul_one, hdeg]
  have htower : Module.finrank F F' = Module.finrank F F⟮y⟯ * Module.finrank F⟮y⟯ F' :=
    (Module.finrank_mul_finrank F F⟮y⟯ F').symm
  rw [adjoin.finrank hyint, hdegy] at htower
  have hn : 0 < Module.finrank F F' := Module.finrank_pos
  have hm : Module.finrank F⟮y⟯ F' = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hn
    rw [mul_one]
    apply htower.symm
  have hnormy : Algebra.norm F y = (-1) ^ Module.finrank F F' * (minpoly F x).eval c := by
    rw [Algebra.norm_eq_norm_adjoin, hm, pow_one, ← adjoin.powerBasis_gen hyint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_gen, minpoly_gen,
      adjoin.powerBasis_dim, hdegy, hminy, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X,
      eval_C, zero_add]
  have hneg : algebraMap F F' c - x = algebraMap F F' (-1) * y := by
    rw [map_neg, map_one, neg_one_mul, hy, neg_sub]
  rw [hneg, map_mul, Algebra.norm_algebraMap, hnormy, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
    one_pow, one_mul]


-- created on 2026-10-13
