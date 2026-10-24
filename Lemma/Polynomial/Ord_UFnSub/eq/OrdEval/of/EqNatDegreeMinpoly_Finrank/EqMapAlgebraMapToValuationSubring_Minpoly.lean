import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Lemma.Int.P2MUtil

open Polynomial IntermediateField AlgebraicCurve
open AlgebraicCurve

/--
[AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval.lean)
-/

private lemma  norm_algebraMap_sub
    {F F' : Type*}
    [Field F]
    [Field F']
    [Algebra F F']
    [Module.Finite F F']
    (x : F') (hdeg : (minpoly F x).natDegree = Module.finrank F F') (c : F) :
    Algebra.norm F (algebraMap F F' c - x) = (minpoly F x).eval c := by
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
    have h : Module.finrank F F' * Module.finrank F⟮y⟯ F' = Module.finrank F F' * 1 := by
      rw [mul_one]; exact htower.symm
    exact Nat.eq_of_mul_eq_mul_left hn h

  have hnormy : Algebra.norm F y = (-1) ^ Module.finrank F F' * (minpoly F x).eval c := by
    rw [Algebra.norm_eq_norm_adjoin, hm, pow_one, ← adjoin.powerBasis_gen hyint,
      Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, adjoin.powerBasis_gen, minpoly_gen, adjoin.powerBasis_dim,
      hdegy, hminy, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_C, zero_add]
  have hneg : algebraMap F F' c - x = algebraMap F F' (-1) * y := by
    rw [map_neg, map_one, neg_one_mul, hy, neg_sub]
  rw [hneg, map_mul, Algebra.norm_algebraMap, hnormy, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
    one_mul]



open AlgebraicCurve

private lemma  ord_norm_sub_eq
    {K F F' : Type*}
    [Field K]
    [Field F]
    [Field F']
    [Algebra K F]
    [Algebra F F']
    [Module.Finite F F']
    (v : Place K F) (Q : Polynomial v.toValuationSubring) {x : F'}
    (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x)
    (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) :
    v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F) := by
  have h1 : x - algebraMap F F' (b : F) = -(algebraMap F F' (b : F) - x) := (neg_sub _ _).symm
  have h2 : Algebra.norm F (-(algebraMap F F' (b : F) - x))
      = (-1) ^ Module.finrank F F' * Algebra.norm F (algebraMap F F' (b : F) - x) := by
    have hneg1 : (-1 : F') = algebraMap F F' (-1) := by simp
    rw [neg_eq_neg_one_mul, map_mul, hneg1, Algebra.norm_algebraMap]
  have h3 : ((Q.eval b : v.toValuationSubring) : F) = (minpoly F x).eval (b : F) := by
    rw [← hQ, eval_map]
    exact (eval₂_at_apply (algebraMap v.toValuationSubring F) b).symm
  rw [h1, h2, norm_algebraMap_sub x hdeg, h3]
  rcases neg_one_pow_eq_or F (Module.finrank F F') with h | h
  · rw [h, one_mul]
  · rw [h, neg_one_mul, Place.ord_neg]
@[path]
private lemma main
  {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F'] [Module.Finite F F']
  {v : Place K F}
  {Q : Polynomial v.toValuationSubring}
  {x : F'}
  {b : v.toValuationSubring}
-- given
  (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x)
  (hdeg : (minpoly F x).natDegree = Module.finrank F F') :
-- imply
  v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F) := by
-- proof
  exact ord_norm_sub_eq v Q hQ hdeg b


-- created on 2026-10-23
