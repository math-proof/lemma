import Mathlib
import sympy.Basic
import sympy.polys.agca.elliptic_curve.point_count

open WeierstrassCurve.Affine Polynomial
open Polynomial


namespace WeierstrassCurve.Affine

/--
[frobeniusTrace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
lemma frobeniusTrace_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) :=
-- proof
  rfl

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[natCard_point_eq_natCard_affineSolutions_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
lemma natCard_point_eq_natCard_affineSolutions_add_one
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
-- imply
  Nat.card W.Point = Nat.card (Subtype (fun xy : Prod F F => W.Equation xy.fst xy.snd)) + 1 := by
-- proof
  calc
    Nat.card W.Point =
      Nat.card (WithZero {xy : F × F // W.Equation xy.1 xy.2}) :=
      Nat.card_congr W.pointEquiv
    _ = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 := by
      change Nat.card (Option {xy : F × F // W.Equation xy.1 xy.2}) = _
      exact Finite.card_option

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

variable {R : Type u} [CommRing R] (W : Affine R)
variable {F : Type u} [Field F]
variable (W : Affine F)
/--
[equationPolynomial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma equationPolynomial_ne_zero (x : F) : equationPolynomial W x ≠ 0 := by
  apply Polynomial.Monic.ne_zero
  unfold equationPolynomial
  monicity <;> norm_num

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

variable {R : Type u} [CommRing R] (W : Affine R)
variable {F : Type u} [Field F]
variable (W : Affine F)
/--
[equationPolynomial_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma equationPolynomial_natDegree (x : F) :
  (equationPolynomial W x).natDegree = 2 := by
  unfold equationPolynomial
  compute_degree <;> norm_num

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

variable {R : Type u} [CommRing R] (W : Affine R)
variable {F : Type u} [Field F]
variable (W : Affine F)
/--
[equation_iff_eval_equationPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma equation_iff_eval_equationPolynomial (x y : F) :
  W.Equation x y ↔ (equationPolynomial W x).eval y = 0 := by
  rw [equation_iff]
  simp only [equationPolynomial, eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  constructor <;> intro h <;> linear_combination h

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

variable {R : Type u} [CommRing R] (W : Affine R)
variable {F : Type u} [Field F]
variable (W : Affine F)
/--
[equationFiber_natCard_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
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

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[natCard_point_le_two_mul_natCard_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
lemma natCard_point_le_two_mul_natCard_add_one
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  Nat.card W.Point ≤ 2 * Nat.card F + 1 := by
-- proof
  let _ : Fintype F := Fintype.ofFinite F
  let encode : W.Point → Option {xy : F × F // W.Equation xy.1 xy.2}
    | .zero => none
    | .some x y h => some ⟨(x, y), h.1⟩
  have hinj : Function.Injective encode := by
    intro P Q h
    cases P <;> cases Q <;> simp_all [encode]
  calc
    Nat.card W.Point ≤ Nat.card (Option {xy : F × F // W.Equation xy.1 xy.2}) :=
      Nat.card_le_card_of_injective encode hinj
    _ = Nat.card {xy : F × F // W.Equation xy.1 xy.2} + 1 :=
      Finite.card_option
    _ =
      (∑ x : F, Nat.card {y : F // W.Equation x y}) + 1 := by
      rw [Nat.card_congr (affineSolutionsEquivSigma W), Nat.card_sigma]
    _ ≤ (∑ _x : F, 2) + 1 := by
      gcongr with x
      exact equationFiber_natCard_le_two W x
    _ = 2 * Nat.card F + 1 := by simp [Nat.card_eq_fintype_card, mul_comm]

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[natCard_point_eq_natCard_add_one_sub_frobeniusTrace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
lemma natCard_point_eq_natCard_add_one_sub_frobeniusTrace
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace := by
-- proof
  rw [frobeniusTrace]
  ring

end WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

/--
[natCard_point_add_frobeniusTrace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
lemma natCard_point_add_frobeniusTrace_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 := by
-- proof
  rw [frobeniusTrace]
  ring

end WeierstrassCurve.Affine


-- created on 2026-10-09
-- updated on 2026-10-23
