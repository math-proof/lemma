import Mathlib
import sympy.Basic
import sympy.AlgebraicGeometry.EllipticCurve.PointCount

open WeierstrassCurve.Affine Polynomial

/--
[frobeniusTrace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma frobeniusTrace_eq_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  W.frobeniusTrace = (Nat.card F : ℤ) + 1 - (Nat.card W.Point : ℤ) := by
-- proof
  apply WeierstrassCurve.Affine.frobeniusTrace_eq


/--
[natCard_point_eq_natCard_affineSolutions_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma natCard_point_eq_natCard_affineSolutions_add_one_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
-- imply
  Nat.card W.Point = Nat.card (Subtype (fun xy : Prod F F => W.Equation xy.fst xy.snd)) + 1 := by
-- proof
  apply WeierstrassCurve.Affine.natCard_point_eq_natCard_affineSolutions_add_one


/--
[natCard_point_le_two_mul_natCard_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma natCard_point_le_two_mul_natCard_add_one_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  Nat.card W.Point ≤ 2 * Nat.card F + 1 := by
-- proof
  apply WeierstrassCurve.Affine.natCard_point_le_two_mul_natCard_add_one


/--
[natCard_point_eq_natCard_add_one_sub_frobeniusTrace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma natCard_point_eq_natCard_add_one_sub_frobeniusTrace_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  (Nat.card W.Point : ℤ) = (Nat.card F : ℤ) + 1 - W.frobeniusTrace := by
-- proof
  apply WeierstrassCurve.Affine.natCard_point_eq_natCard_add_one_sub_frobeniusTrace


/--
[natCard_point_add_frobeniusTrace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/PointCount.lean)
-/
@[path]
private lemma natCard_point_add_frobeniusTrace_eq_eq
  [Field F] [Finite F]
-- given
  (W : WeierstrassCurve.Affine F) :
-- imply
  (Nat.card W.Point : ℤ) + W.frobeniusTrace = (Nat.card F : ℤ) + 1 := by
-- proof
  apply WeierstrassCurve.Affine.natCard_point_add_frobeniusTrace_eq


-- created on 2026-10-09
