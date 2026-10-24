import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardTheta
open StatMech StatMech.FrontierA


/--
[kwTheta_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTheta.lean)
-/
@[path]
private lemma kwTheta_one_sub_eq
  {omega : ℂ}
-- given
  (x : Fin 3 -> ℂ) :
-- imply
  1 - kwThetaTransition omega x = Matrix.fromBlocks 1 (-kwThetaForward omega x) (-kwThetaReverse omega x) 1 := by
-- proof
  apply StatMech.FrontierA.kwTheta_one_sub omega x

/--
[kacWard_theta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTheta.lean)
-/
@[path]
private lemma kacWard_theta_eq
  {omega : ℂ}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (x : Fin 3 -> ℂ) :
-- imply
  (1 - kwThetaTransition omega x).det = (kwThetaEvenPolynomial x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_theta omega homega hI x


-- created on 2026-10-23
