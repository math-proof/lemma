import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Def.AlgebraicGeometry.EllipticCurve.PointCount.Part3
open Polynomial

/-!
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/


namespace WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] (W : Affine R)

variable {F : Type u} [Field F]

variable (W : Affine F)

lemma equationPolynomial_ne_zero (x : F) : equationPolynomial W x ≠ 0 := by
  apply Polynomial.Monic.ne_zero
  unfold equationPolynomial
  monicity <;> norm_num

lemma equationPolynomial_natDegree (x : F) :
    (equationPolynomial W x).natDegree = 2 := by
  unfold equationPolynomial
  compute_degree <;> norm_num

lemma equation_iff_eval_equationPolynomial (x y : F) :
    W.Equation x y ↔ (equationPolynomial W x).eval y = 0 := by
  rw [equation_iff]
  simp only [equationPolynomial, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  constructor <;> intro h <;> linear_combination h

lemma equationFiber_natCard_le_two [Finite F] (x : F) :
    Nat.card {y : F // W.Equation x y} ≤ 2 := by
  rw [show Nat.card {y : F // W.Equation x y} =
      Set.ncard {y : F | W.Equation x y} from rfl]
  rw [show {y : F | W.Equation x y} = (equationPolynomial W x).rootSet F by
    ext y
    rw [Polynomial.mem_rootSet, and_iff_right (equationPolynomial_ne_zero W x)]
    simpa [aeval_def] using equation_iff_eval_equationPolynomial W x y]
  calc
    ((equationPolynomial W x).rootSet F).ncard ≤
        (equationPolynomial W x).natDegree :=
      Polynomial.ncard_rootSet_le _ _
    _ = 2 := equationPolynomial_natDegree W x

end WeierstrassCurve.Affine
