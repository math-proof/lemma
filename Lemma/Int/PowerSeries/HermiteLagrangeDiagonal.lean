import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.PowerSeries.HermiteLagrangeDiagonal
open PowerSeries
open MetaMathlibExt.LagrangeInversion


/--
[coeff_mul_pow_eq_coeff_of_eq_X_mul_subst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
private lemma coeff_mul_pow_eq_coeff_of_eq_X_mul_subst_eq
  [CommRing R]
  {n : ℕ}
  {F phi w G : PowerSeries R}
-- given
  (hw : w = PowerSeries.X * phi.subst w)
  (hG : (1 - PowerSeries.X * (PowerSeries.derivative phi).subst w) * G = F.subst w) :
-- imply
  (PowerSeries.coeff n) (F * phi ^ n) = (PowerSeries.coeff n) G := by
-- proof
  apply MetaMathlibExt.LagrangeInversion.coeff_mul_pow_eq_coeff_of_eq_X_mul_subst n hw hG

/--
[hermite_lagrange_diagonal_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PowerSeries/HermiteLagrangeDiagonal.lean)
-/
@[path]
private lemma hermite_lagrange_diagonal_formula_eq
  [CommRing R]
  {n : ℕ}
  {F phi w G : PowerSeries R}
-- given
  (hw0 : PowerSeries.constantCoeff w = 0)
  (hphi : PowerSeries.coeff 0 phi ≠ 0)
  (hw : w = PowerSeries.X * phi.subst w)
  (hG : (1 - PowerSeries.X * (PowerSeries.derivative phi).subst w) * G = F.subst w) :
-- imply
  (PowerSeries.coeff n) (F * phi ^ n) = (PowerSeries.coeff n) G := by
-- proof
  apply MetaMathlibExt.LagrangeInversion.hermite_lagrange_diagonal_formula n R F phi w hw0 hphi hw G hG


-- created on 2026-10-20
