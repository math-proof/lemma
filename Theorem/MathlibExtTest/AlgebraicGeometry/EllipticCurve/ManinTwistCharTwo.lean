/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/EllipticCurve/ManinTwistCharTwo.lean -/

import Theorem.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part22
import Lemma.Scheme.EllipticCurve.ManinTwistCharTwo
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum
import Instance.MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo.Part2


namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo

open WeierstrassCurve

open MathlibExt.AlgebraicGeometry.EllipticCurve

/-- The `q = 2` construction does not need a normal-form hypothesis. -/
example : Nonempty (ManinDegreeData
    (Nat.card (ZMod 2)) (Nat.card ordinaryCurve.toAffine.Point)) :=
  ManinTwistCharTwo.manin_degree_data_of_card_eq_two (by norm_num) ordinaryCurve

/-- The elementary small-field construction also covers every equation over the field of order
four. -/
example (W : WeierstrassCurve (GaloisField 2 2)) : Nonempty (ManinDegreeData
    (Nat.card (GaloisField 2 2)) (Nat.card W.toAffine.Point)) :=
  ManinTwistCharTwo.manin_degree_data_of_card_eq_four
    (GaloisField.card 2 2 (by norm_num)) W

/-- Manin's characteristic-two construction produces the complete degree data. -/
example : Nonempty (ManinDegreeData
    (Nat.card (ZMod 2)) (Nat.card ordinaryCurve.toAffine.Point)) := by
  let _ : ordinaryCurve.IsCharTwoNF := .of_j_ne_zero
  exact ManinTwistCharTwo.manin_degree_data_of_isCharTwoNF ordinaryCurve

/-- The ordinary characteristic-two case applies over `ZMod 2`. -/
example :
    (((Nat.card (ZMod 2) : ℤ) + 1 -
        (Nat.card ordinaryCurve.toAffine.Point : ℤ)) ^ 2 ≤
      4 * (Nat.card (ZMod 2) : ℤ)) :=
  ManinTwistCharTwo.hasse_bound_of_isCharTwoJNeZeroNF ordinaryCurve

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ManinTwistCharTwo
