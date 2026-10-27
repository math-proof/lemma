import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
open StatMech StatMech.FrontierA StatMech.FrontierA.RibbonPermutationSystem


/--
[permCycleCount_add_cycleType_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma permCycleCount_add_cycleType_sum_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  permCycleCount sigma + sigma.cycleType.sum = Fintype.card D + Multiset.card sigma.cycleType := by
-- proof
  apply StatMech.FrontierA.permCycleCount_add_cycleType_sum sigma

/--
[card_add_permCycleCount_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma card_add_permCycleCount_mod_two_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  (Fintype.card D + permCycleCount sigma) % 2 = (sigma.cycleType.sum + Multiset.card sigma.cycleType) % 2 := by
-- proof
  apply StatMech.FrontierA.card_add_permCycleCount_mod_two sigma

/--
[perm_sign_val_eq_neg_one_pow_cycleCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma perm_sign_val_eq_neg_one_pow_cycleCount_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D} :
-- imply
  ((Equiv.Perm.sign sigma : Units Int) : Int) = (-1 : Int) ^ (Fintype.card D + permCycleCount sigma) := by
-- proof
  apply StatMech.FrontierA.perm_sign_val_eq_neg_one_pow_cycleCount sigma

/--
[permCycleCount_mod_two_toggle_of_sign_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma permCycleCount_mod_two_toggle_of_sign_neg_eq
  [Fintype D]
  [DecidableEq D]
  {sigma tau : Equiv.Perm D}
-- given
  (hsign : ((Equiv.Perm.sign tau : Units Int) : Int) = -((Equiv.Perm.sign sigma : Units Int) : Int)) :
-- imply
  permCycleCount tau % 2 = (permCycleCount sigma + 1) % 2 := by
-- proof
  apply StatMech.FrontierA.permCycleCount_mod_two_toggle_of_sign_neg sigma tau hsign

/--
[partialEdgeFlip_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma partialEdgeFlip_insert_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E}
  {e : E}
-- given
  (he : e ∈ F -> False) :
-- imply
  R.partialEdgeFlip (insert e F) = R.edgeFlip e * R.partialEdgeFlip F := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.partialEdgeFlip_insert R F e he

/--
[boundaryPerm_insert_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma boundaryPerm_insert_sign_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E}
  {e : E}
-- given
  (he : e ∈ F -> False) :
-- imply
  ((Equiv.Perm.sign (R.boundaryPerm (insert e F)) : Units Int) : Int) = -((Equiv.Perm.sign (R.boundaryPerm F) : Units Int) : Int) := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm_insert_sign R F e he

/--
[boundaryComponents_insert_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma boundaryComponents_insert_mod_two_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {F : Finset E}
  {e : E}
-- given
  (he : e ∈ F -> False) :
-- imply
  R.boundaryComponents (insert e F) % 2 = (R.boundaryComponents F + 1) % 2 := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.boundaryComponents_insert_mod_two R F e he

/--
[boundaryPerm_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma boundaryPerm_empty_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D} :
-- imply
  R.boundaryPerm (∅ : Finset E) = R.rotation := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.boundaryPerm_empty R

/--
[boundaryComponents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma boundaryComponents_empty_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D} :
-- imply
  R.boundaryComponents (∅ : Finset E) = permCycleCount R.rotation := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.boundaryComponents_empty R

/--
[boundaryParity_eq_dualVertexCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialRibbonBoundaryParity.lean)
-/
@[path]
private lemma boundaryParity_eq_dualVertexCount_eq
  [Fintype D]
  [DecidableEq D]
  {R : RibbonPermutationSystem E D}
  {dualVertexCount : Nat}
-- given
  (hEuler : (Fintype.card E + permCycleCount R.rotation) % 2 = dualVertexCount % 2) :
-- imply
  forall F : Finset E, (Fᶜ.card + R.boundaryComponents F) % 2 = dualVertexCount % 2 := by
-- proof
  apply StatMech.FrontierA.RibbonPermutationSystem.boundaryParity_eq_dualVertexCount R dualVertexCount hEuler


-- created on 2026-10-23
