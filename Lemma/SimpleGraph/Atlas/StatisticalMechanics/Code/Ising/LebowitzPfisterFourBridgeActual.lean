import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeActual
open Finset SimpleGraph StatMech StatMech.Ising


/--
[fourBridgeSites_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeSites_zero_eq
  {w x y z : V} :
-- imply
  fourBridgeSites w x y z 0 = w := by
-- proof
  apply StatMech.Ising.fourBridgeSites_zero w x y z

/--
[fourBridgeSites_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeSites_one_eq
  {w x y z : V} :
-- imply
  fourBridgeSites w x y z 1 = x := by
-- proof
  apply StatMech.Ising.fourBridgeSites_one w x y z

/--
[fourBridgeSites_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeSites_two_eq
  {w x y z : V} :
-- imply
  fourBridgeSites w x y z 2 = y := by
-- proof
  apply StatMech.Ising.fourBridgeSites_two w x y z

/--
[fourBridgeSites_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeSites_three_eq
  {w x y z : V} :
-- imply
  fourBridgeSites w x y z 3 = z := by
-- proof
  apply StatMech.Ising.fourBridgeSites_three w x y z

/--
[replicaBridgeMoment_fourBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeMoment_fourBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMoment G J hf (fourBridgeSites w x y z) r = Real.cosh r ^ 4 + Real.cosh r ^ 3 * Real.sinh r * fourBridgeOneCoeff G J hf w x y z + Real.cosh r ^ 2 * Real.sinh r ^ 2 * fourBridgeTwoCoeff G J hf w x y z + Real.cosh r * Real.sinh r ^ 3 * fourBridgeThreeCoeff G J hf w x y z + Real.sinh r ^ 4 * fourBridgeFourCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_fourBridgeSites_eq G J hf w x y z r

/--
[replicaBridgeMoment_fourBridgeSites_eq_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeMoment_fourBridgeSites_eq_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMoment G J hf (fourBridgeSites w x y z) r = Real.cosh r ^ 4 * (1 + fourBridgeOneCoeff G J hf w x y z * Real.tanh r + fourBridgeTwoCoeff G J hf w x y z * Real.tanh r ^ 2 + fourBridgeThreeCoeff G J hf w x y z * Real.tanh r ^ 3 + fourBridgeFourCoeff G J hf w x y z * Real.tanh r ^ 4) := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_fourBridgeSites_eq_factor G J hf w x y z r

/--
[replicaBridgeMean_fourBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeMean_fourBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMean G J hf (fourBridgeSites w x y z) r = fourBridgeTiltMean (Real.tanh r) (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_fourBridgeSites_eq G J hf w x y z r

/--
[replicaBridgeVariance_fourBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeVariance_fourBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeVariance G J hf (fourBridgeSites w x y z) r = fourBridgeTiltVariance (Real.tanh r) (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_fourBridgeSites_eq G J hf w x y z r

/--
[replicaBridgeVariance_fourBridgeSites_le_neg_iff_skew](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeVariance_fourBridgeSites_le_neg_iff_skew_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hr : 0 < r) :
-- imply
  replicaBridgeVariance G J hf (fourBridgeSites w x y z) r <= replicaBridgeVariance G J hf (fourBridgeSites w x y z) (-r) <-> fourBridgeVarianceSkewPolynomial (Real.tanh r) (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) <= 0 := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_fourBridgeSites_le_neg_iff_skew G J hf w x y z hr

/--
[fourBridge_allDisagreementCoefficient_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridge_allDisagreementCoefficient_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= 1 - fourBridgeOneCoeff G J hf w x y z + fourBridgeTwoCoeff G J hf w x y z - fourBridgeThreeCoeff G J hf w x y z + fourBridgeFourCoeff G J hf w x y z := by
-- proof
  apply StatMech.Ising.fourBridge_allDisagreementCoefficient_nonneg G J hf w x y z

/--
[fourBridgeRankMass_zero_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeRankMass_zero_le_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 0 <= fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_zero_le_four G J hf w x y z

/--
[fourBridgeRankMass_two_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeRankMass_two_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 2 := by
-- proof
  apply StatMech.Ising.fourBridgeRankMass_two_nonneg G J hf w x y z

/--
[fourBridgeVarianceSkewBernsteinCoeff_five_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_five_factor_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : Real} :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b c d 5 = (1 - a + b - c + d) * (1 + a + b + c + d) * (2 * a * b + 3 * a * d - 3 * a - b * c - 6 * c) / 3 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_five_factor a b c d

/--
[fourBridgeVarianceSkewBernsteinCoeff_six_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_six_factor_eq
  [Fintype V]
  [DecidableEq V]
  {a b c d : Real} :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff a b c d 6 = (1 - a + b - c + d) * (1 + a + b + c + d) * (a * b + 3 * a * d - a - b * c + c * d - 3 * c) := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_six_factor a b c d

/--
[fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos_of_rankCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeActual.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos_of_rankCross_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hcross : fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 0 * fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 3 <= fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 1 * fourBridgeRankMass (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 4) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 5 <= 0 ∧ fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G J hf w x y z) (fourBridgeTwoCoeff G J hf w x y z) (fourBridgeThreeCoeff G J hf w x y z) (fourBridgeFourCoeff G J hf w x y z) 6 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeVarianceSkewBernsteinCoeff_five_six_nonpos_of_rankCross G J hf w x y z hcross


-- created on 2026-10-23
