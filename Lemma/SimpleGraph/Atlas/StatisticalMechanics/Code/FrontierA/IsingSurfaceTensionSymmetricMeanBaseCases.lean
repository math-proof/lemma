import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases.Part2
open StatMech StatMech.FrontierA


/--
[fis_interface_eq_empty_of_right_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean)
-/
@[path]
private lemma fis_interface_eq_empty_of_right_empty_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [IsEmpty W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K) :
-- imply
  StatMech.FK.fis_interface G H K = ∅ := by
-- proof
  apply StatMech.FrontierA.fis_interface_eq_empty_of_right_empty G H K hcross

/--
[unequalReplicaBridgeInteraction_eq_zero_of_right_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean)
-/
@[path]
private lemma unequalReplicaBridgeInteraction_eq_zero_of_right_empty_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [IsEmpty W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {a : ConfigSpace V}
  {b : ConfigSpace W}
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K) :
-- imply
  unequalReplicaBridgeInteraction G H K a b = 0 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeInteraction_eq_zero_of_right_empty G H K hcross a b

/--
[unequalReplicaBridgeMean_eq_zero_of_right_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean)
-/
@[path]
private lemma unequalReplicaBridgeMean_eq_zero_of_right_empty_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [IsEmpty W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
  {r : Real}
-- given
  (hcross : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeMean G H K J hf hg r = 0 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeMean_eq_zero_of_right_empty G H K hcross J hf hg r

/--
[oddPrismUnequalBridgeMean_zero_prism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeMean_zero_prism_eq
  {beta r : Real} :
-- imply
  unequalReplicaBridgeMean (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0) (oddPrismUnequalGlueGraph 0) beta (fun v => beta * oddPrismPlusField 0 v.1) (fun v => beta * oddPrismPlusField 0 v.1) r = 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeMean_zero_prism beta r

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism_eq
  {beta : Real} :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder beta 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism beta

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_zero_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_zero_coupling_eq
  {n : Nat} :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder 0 n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_zero_coupling n


-- created on 2026-10-23
