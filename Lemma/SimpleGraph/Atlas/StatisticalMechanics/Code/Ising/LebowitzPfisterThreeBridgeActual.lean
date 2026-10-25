import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterThreeBridgeActual.Part2
open Finset SimpleGraph StatMech StatMech.Ising


/--
[threeBridgeSites_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma threeBridgeSites_zero_eq
  {x y z : V} :
-- imply
  threeBridgeSites x y z 0 = x := by
-- proof
  apply StatMech.Ising.threeBridgeSites_zero x y z

/--
[threeBridgeSites_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma threeBridgeSites_one_eq
  {x y z : V} :
-- imply
  threeBridgeSites x y z 1 = y := by
-- proof
  apply StatMech.Ising.threeBridgeSites_one x y z

/--
[threeBridgeSites_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma threeBridgeSites_two_eq
  {x y z : V} :
-- imply
  threeBridgeSites x y z 2 = z := by
-- proof
  apply StatMech.Ising.threeBridgeSites_two x y z

/--
[replicaBridgeInteraction_threeBridgeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeInteraction_threeBridgeSites_eq
  {x y z : V}
  {a b : ConfigSpace V} :
-- imply
  replicaBridgeInteraction (threeBridgeSites x y z) a b = spin a x * spin b x + spin a y * spin b y + spin a z * spin b z := by
-- proof
  apply StatMech.Ising.replicaBridgeInteraction_threeBridgeSites x y z a b

/--
[hasDerivAt_threeBridgeTiltMean_tanh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma hasDerivAt_threeBridgeTiltMean_tanh_eq
  [Fintype V]
  [DecidableEq V]
  {r a b c : Real}
-- given
  (hP : 1 + a * Real.tanh r + b * Real.tanh r ^ 2 + c * Real.tanh r ^ 3 ≠ 0) :
-- imply
  HasDerivAt (fun u => threeBridgeTiltMean (Real.tanh u) a b c) (threeBridgeTiltVariance (Real.tanh r) a b c) r := by
-- proof
  apply StatMech.Ising.hasDerivAt_threeBridgeTiltMean_tanh r a b c hP

/--
[replicaBridgeMoment_threeBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeMoment_threeBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMoment G J hf (threeBridgeSites x y z) r = Real.cosh r ^ 3 + Real.cosh r ^ 2 * Real.sinh r * threeBridgeOneCoeff G J hf x y z + Real.cosh r * Real.sinh r ^ 2 * threeBridgeTwoCoeff G J hf x y z + Real.sinh r ^ 3 * threeBridgeThreeCoeff G J hf x y z := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_threeBridgeSites_eq G J hf x y z r

/--
[replicaBridgeMoment_threeBridgeSites_eq_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeMoment_threeBridgeSites_eq_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMoment G J hf (threeBridgeSites x y z) r = Real.cosh r ^ 3 * (1 + threeBridgeOneCoeff G J hf x y z * Real.tanh r + threeBridgeTwoCoeff G J hf x y z * Real.tanh r ^ 2 + threeBridgeThreeCoeff G J hf x y z * Real.tanh r ^ 3) := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_threeBridgeSites_eq_factor G J hf x y z r

/--
[replicaBridgeMean_threeBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeMean_threeBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMean G J hf (threeBridgeSites x y z) r = threeBridgeTiltMean (Real.tanh r) (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_threeBridgeSites_eq G J hf x y z r

/--
[replicaBridgeVariance_threeBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeVariance_threeBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeVariance G J hf (threeBridgeSites x y z) r = threeBridgeTiltVariance (Real.tanh r) (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_threeBridgeSites_eq G J hf x y z r

/--
[replicaBridgeVariance_threeBridgeSites_le_neg_iff_skew](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma replicaBridgeVariance_threeBridgeSites_le_neg_iff_skew_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hr : 0 < r) :
-- imply
  replicaBridgeVariance G J hf (threeBridgeSites x y z) r <= replicaBridgeVariance G J hf (threeBridgeSites x y z) (-r) <-> threeBridgeVarianceSkewPolynomial (Real.tanh r) (threeBridgeOneCoeff G J hf x y z) (threeBridgeTwoCoeff G J hf x y z) (threeBridgeThreeCoeff G J hf x y z) <= 0 := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_threeBridgeSites_le_neg_iff_skew G J hf x y z hr

/--
[threeBridgeThreeCoeff_le_grahamBoundSq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma threeBridgeThreeCoeff_le_grahamBoundSq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {i j k : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall v, 0 <= hf v)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  threeBridgeThreeCoeff G K hf i j k <= (grahamInhomOne G K hf i * expJ G.edgeFinset K hf (fun s => spin s j * spin s k) + expJ G.edgeFinset K hf (fun s => spin s i * spin s j) * grahamInhomOne G K hf k + expJ G.edgeFinset K hf (fun s => spin s i * spin s k) * grahamInhomOne G K hf j - 2 * grahamInhomOne G K hf i * grahamInhomOne G K hf j * grahamInhomOne G K hf k - 2 * ghsiCovariance G K hf i k * ghsiCovariance G K hf j k * grahamInhomOne G K hf k) ^ 2 := by
-- proof
  apply StatMech.Ising.threeBridgeThreeCoeff_le_grahamBoundSq G K hf hK hhf hij hik hjk

/--
[threeBridge_allDisagreementCoefficient_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterThreeBridgeActual.lean)
-/
@[path]
private lemma threeBridge_allDisagreementCoefficient_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y z : V}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  0 <= 1 - threeBridgeOneCoeff G J hf x y z + threeBridgeTwoCoeff G J hf x y z - threeBridgeThreeCoeff G J hf x y z := by
-- proof
  apply StatMech.Ising.threeBridge_allDisagreementCoefficient_nonneg G J hf x y z


-- created on 2026-10-23
