import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Point counts of elliptic curves over finite fields

This file defines the Frobenius trace of an elliptic curve over a finite field through its rational
point count. It also supplies a finiteness instance for the canonical affine point type.
-/

open Polynomial

namespace WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] (W : Affine R)

namespace Point

/-- The nonsingular points of a Weierstrass curve over a finite commutative ring form a finite
type. The point at infinity is included. -/
instance instFinitePoint [Finite R] : Finite W.Point := by
  let _ : Finite (WithZero {xy : Prod R R // W.Nonsingular xy.1 xy.2}) :=
    inferInstanceAs (Finite (Option {xy : Prod R R // W.Nonsingular xy.1 xy.2}))
  exact Finite.of_injective W.nonsingularPointEquiv W.nonsingularPointEquiv.injective

end Point

variable {F : Type u} [Field F]

/-- The Frobenius trace of an elliptic curve over a finite field, defined by
`a_q(E) = q + 1 - #E(𝔽_q)`. The point at infinity belongs to `W.Point`. -/
noncomputable def frobeniusTrace (W : Affine F) [Finite F] : ℤ :=
  (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ)

variable (W : Affine F)

theorem frobeniusTrace_eq [Finite F] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) :=
  rfl

/-- The rational-point count is one plus the number of affine solutions to the Weierstrass
equation; the extra point is the point at infinity. -/
theorem natCard_point_eq_natCard_affineSolutions_add_one [Finite F] [W.IsElliptic] :
    Nat.card W.Point = Nat.card {xy : Prod F F // W.Equation xy.1 xy.2} + 1 := by
  calc
    Nat.card W.Point =
        Nat.card (WithZero {xy : Prod F F // W.Equation xy.1 xy.2}) :=
      Nat.card_congr W.pointEquiv
    _ = Nat.card {xy : Prod F F // W.Equation xy.1 xy.2} + 1 := by
      change Nat.card (Option {xy : Prod F F // W.Equation xy.1 xy.2}) = _
      exact Finite.card_option

private noncomputable def equationPolynomial (x : F) : F[X] :=
  X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)

private lemma equationPolynomial_ne_zero (x : F) : equationPolynomial W x ≠ 0 := by
  apply Polynomial.Monic.ne_zero
  unfold equationPolynomial
  monicity <;> norm_num

private lemma equationPolynomial_natDegree (x : F) :
    (equationPolynomial W x).natDegree = 2 := by
  unfold equationPolynomial
  compute_degree <;> norm_num

private lemma equation_iff_eval_equationPolynomial (x y : F) :
    W.Equation x y ↔ (equationPolynomial W x).eval y = 0 := by
  rw [equation_iff]
  simp only [equationPolynomial, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  constructor <;> intro h <;> linear_combination h

private lemma equationFiber_natCard_le_two [Finite F] (x : F) :
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

private def affineSolutionsEquivSigma :
    {xy : Prod F F // W.Equation xy.1 xy.2} ≃ Σ x : F, {y : F // W.Equation x y} where
  toFun xy := ⟨xy.1.1, xy.1.2, xy.2⟩
  invFun xy := ⟨(xy.1, xy.2.1), xy.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A Weierstrass equation over a finite field has at most two affine points over each
`x`-coordinate, plus the point at infinity. -/
theorem natCard_point_le_two_mul_natCard_add_one [Finite F] :
    Nat.card W.Point ≤ 2 * Nat.card F + 1 := by
  let _ : Fintype F := Fintype.ofFinite F
  let encode : W.Point → Option {xy : Prod F F // W.Equation xy.1 xy.2}
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  have hinj : Function.Injective encode := by
    intro P Q h
    cases P <;> cases Q <;> simp_all [encode]
  calc
    Nat.card W.Point ≤ Nat.card (Option {xy : Prod F F // W.Equation xy.1 xy.2}) :=
      Nat.card_le_card_of_injective encode hinj
    _ = Nat.card {xy : Prod F F // W.Equation xy.1 xy.2} + 1 :=
      Finite.card_option
    _ =
        (∑ x : F, Nat.card {y : F // W.Equation x y}) + 1 := by
      rw [Nat.card_congr (affineSolutionsEquivSigma W), Nat.card_sigma]
    _ ≤ (∑ _x : F, 2) + 1 := by
      gcongr with x
      exact equationFiber_natCard_le_two W x
    _ = 2 * Nat.card F + 1 := by simp [Nat.card_eq_fintype_card, mul_comm]

/-- The point-count formula rearranged as `#E(𝔽_q) = q + 1 - a_q(E)`. -/
theorem natCard_point_eq_natCard_add_one_sub_frobeniusTrace [Finite F] :
    (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace := by
  rw [frobeniusTrace]
  ring

/-- The point count and Frobenius trace sum to `q + 1`. -/
theorem natCard_point_add_frobeniusTrace_eq [Finite F] :
    (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 := by
  rw [frobeniusTrace]
  ring

end WeierstrassCurve.Affine
