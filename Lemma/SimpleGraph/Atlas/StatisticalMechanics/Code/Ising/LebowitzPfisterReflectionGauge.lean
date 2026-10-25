import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
open Finset StatMech StatMech.Ising


/--
[ghsiCrossExp2_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma ghsiCrossExp2_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiCrossExp2 G J hf hf F = ghsiExp2 G J hf F := by
-- proof
  apply StatMech.Ising.ghsiCrossExp2_same G J hf F

/--
[replicaBridgeInteraction_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaBridgeInteraction_flip_right_eq
  [Fintype V]
  [DecidableEq V]
  {a b : ConfigSpace V}
-- given
  (sites : I -> V) :
-- imply
  replicaBridgeInteraction sites a (FieldGhostDict.flipV b) = -replicaBridgeInteraction sites a b := by
-- proof
  apply StatMech.Ising.replicaBridgeInteraction_flip_right sites a b

/--
[ghsiCrossExp2_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma ghsiCrossExp2_flip_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiCrossExp2 G J hf (fun x => -hf x) F = ghsiExp2 G J hf (fun a b => F a (FieldGhostDict.flipV b)) := by
-- proof
  apply StatMech.Ising.ghsiCrossExp2_flip_right G J hf F

/--
[ghsiExp2_eq_cross_flip_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma ghsiExp2_eq_cross_flip_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiExp2 G J hf F = ghsiCrossExp2 G J hf (fun x => -hf x) (fun a b => F a (FieldGhostDict.flipV b)) := by
-- proof
  apply StatMech.Ising.ghsiExp2_eq_cross_flip_right G J hf F

/--
[ghsiCrossExp2_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma ghsiCrossExp2_neg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (J : Sym2 V -> Real)
  (hf₁ hf₂ : V -> Real)
  (F : ConfigSpace V -> ConfigSpace V -> Real) :
-- imply
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b => -F a b) = -ghsiCrossExp2 G J hf₁ hf₂ F := by
-- proof
  apply StatMech.Ising.ghsiCrossExp2_neg G J hf₁ hf₂ F

/--
[replicaCrossBridgeMoment_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaCrossBridgeMoment_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaCrossBridgeMoment G J hf hf sites r = replicaBridgeMoment G J hf sites r := by
-- proof
  apply StatMech.Ising.replicaCrossBridgeMoment_same G J hf sites r

/--
[replicaBridgeMoment_neg_eq_cross_negField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaBridgeMoment_neg_eq_cross_negField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMoment G J hf sites (-r) = replicaCrossBridgeMoment G J hf (fun x => -hf x) sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeMoment_neg_eq_cross_negField G J hf sites r

/--
[replicaCrossBridgeMean_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaCrossBridgeMean_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaCrossBridgeMean G J hf hf sites r = replicaBridgeMean G J hf sites r := by
-- proof
  apply StatMech.Ising.replicaCrossBridgeMean_same G J hf sites r

/--
[replicaBridgeMean_neg_eq_neg_cross_negField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaBridgeMean_neg_eq_neg_cross_negField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeMean G J hf sites (-r) = -replicaCrossBridgeMean G J hf (fun x => -hf x) sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeMean_neg_eq_neg_cross_negField G J hf sites r

/--
[replicaCrossBridgeVariance_same](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaCrossBridgeVariance_same_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaCrossBridgeVariance G J hf hf sites r = replicaBridgeVariance G J hf sites r := by
-- proof
  apply StatMech.Ising.replicaCrossBridgeVariance_same G J hf sites r

/--
[replicaBridgeVariance_neg_eq_cross_negField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaBridgeVariance_neg_eq_cross_negField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeVariance G J hf sites (-r) = replicaCrossBridgeVariance G J hf (fun x => -hf x) sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_neg_eq_cross_negField G J hf sites r

/--
[replicaBridgeVariance_order_iff_crossField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaBridgeVariance_order_iff_crossField_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V) :
-- imply
  replicaBridgeVariance G J hf sites r <= replicaBridgeVariance G J hf sites (-r) <-> replicaCrossBridgeVariance G J hf hf sites r <= replicaCrossBridgeVariance G J hf (fun x => -hf x) sites r := by
-- proof
  apply StatMech.Ising.replicaBridgeVariance_order_iff_crossField G J hf sites r

/--
[replicaBridgeFreeEnergy_le_of_crossField_variance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectionGauge.lean)
-/
@[path]
private lemma replicaBridgeFreeEnergy_le_of_crossField_variance_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {r : Real}
-- given
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (sites : I -> V)
  (hr : 0 <= r)
  (hcross : forall t, 0 <= t -> replicaCrossBridgeVariance G J hf hf sites t <= replicaCrossBridgeVariance G J hf (fun x => -hf x) sites t) :
-- imply
  replicaBridgeFreeEnergy G J hf sites r <= 2 * r * ∑ i : I, (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
-- proof
  apply StatMech.Ising.replicaBridgeFreeEnergy_le_of_crossField_variance G J hf sites r hr hcross


-- created on 2026-10-23
