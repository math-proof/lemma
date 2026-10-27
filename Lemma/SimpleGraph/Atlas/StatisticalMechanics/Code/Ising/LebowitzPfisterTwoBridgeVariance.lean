import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoBridgeVariance.Part3
open StatMech StatMech.Ising


/--
[replicaBridgeInteraction_twoBridgeSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeInteraction_twoBridgeSites_eq
  [Fintype V]
  [DecidableEq V]
  {x y : V}
  {a b : ConfigSpace V} :
-- imply
  replicaBridgeInteraction (twoBridgeSites x y) a b = spin a x * spin b x + spin a y * spin b y := by
-- proof
  apply StatMech.Ising.replicaBridgeInteraction_twoBridgeSites x y a b

/--
[replicaBridgeMoment_twoBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeMoment_twoBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMoment G J hf (twoBridgeSites x y) r = twoReplicaTwoBridgeMoment G J hf x y r := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_twoBridgeSites_eq G J hf x y r

/--
[replicaBridgeMean_twoBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeMean_twoBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeMean G J hf (twoBridgeSites x y) r = twoBridgeTiltMean (Real.tanh r) ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 + (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) ((expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2) := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_twoBridgeSites_eq G J hf x y r

/--
[hasDerivAt_twoBridgeTiltMean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma hasDerivAt_twoBridgeTiltMean_eq
  [Fintype V]
  [DecidableEq V]
  {t A E : Real}
-- given
  (hP : 1 + A * t + E * t ^ 2 ≠ 0) :
-- imply
  HasDerivAt (fun u => twoBridgeTiltMean u A E) (twoBridgeTiltMeanDeriv t A E) t := by
-- proof
  apply StatMech.Ising.hasDerivAt_twoBridgeTiltMean t A E hP

/--
[replicaBridgeVariance_twoBridgeSites_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeVariance_twoBridgeSites_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real) :
-- imply
  replicaBridgeVariance G J hf (twoBridgeSites x y) r = twoBridgeTiltVariance (Real.tanh r) ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 + (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) ((expJ G.edgeFinset J hf (fun s => spin s x * spin s y)) ^ 2) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_twoBridgeSites_eq G J hf x y r

/--
[replicaBridgeVariance_twoBridgeSites_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeVariance_twoBridgeSites_le_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hr : 0 <= r) :
-- imply
  replicaBridgeVariance G J hf (twoBridgeSites x y) r <= replicaBridgeVariance G J hf (twoBridgeSites x y) (-r) := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_twoBridgeSites_le_neg G J hf hJ hhf x y hxy r hr

/--
[replicaCrossBridgeVariance_twoBridgeSites_same_le_negField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaCrossBridgeVariance_twoBridgeSites_same_le_negField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hr : 0 <= r) :
-- imply
  replicaCrossBridgeVariance G J hf hf (twoBridgeSites x y) r <= replicaCrossBridgeVariance G J hf (fun v => -hf v) (twoBridgeSites x y) r := by
-- proof
  apply StatMech.Ising.replicaCrossBridgeVariance_twoBridgeSites_same_le_negField G J hf hJ hhf x y hxy r hr

/--
[replicaBridgeFreeEnergy_twoBridgeSites_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoBridgeVariance.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_twoBridgeSites_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hJ : forall e, 0 <= J e)
  (hhf : forall v, 0 <= hf v)
  (hxy : x ≠ y)
  (hr : 0 <= r) :
-- imply
  replicaBridgeFreeEnergy G J hf (twoBridgeSites x y) r <= 2 * r * ((expJ G.edgeFinset J hf (fun s => spin s x)) ^ 2 + (expJ G.edgeFinset J hf (fun s => spin s y)) ^ 2) := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_twoBridgeSites_le G J hf hJ hhf x y hxy r hr


-- created on 2026-10-23
