import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector
open StatMech StatMech.FrontierD


/--
[sixVertexDegreeTwoSynchronizedComponentSelector_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentSelector_eq_true_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component dart = true ↔ (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk dart = component := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentSelector_eq_true_iff homega heta hdegree component dart

/--
[sixVertexDegreeTwoSynchronizedComponentSelector_predecessors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentSelector_predecessors_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false dart) = sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentSelector_predecessors homega heta hdegree component dart

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {state : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (doubledAlignedBranchSwap state) = sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component state := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_branchSwap homega heta hdegree component state

/--
[sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree component (dart, false) = sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree component (dart, true) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransitionBit_branches homega heta hdegree component dart

/--
[sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component = ∑ dart : SixVertexOrientedDisagreementDart omega eta, if sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component dart then sixVertexDegreeTwoStrandStepSeamSign hdegree dart else 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentCharge_eq_selectorSum homega heta hdegree component

/--
[sixVertexDegreeTwoSynchronizedComponentSelector_seamSum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitSelector.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentSelector_seamSum_eq_one_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hcharge : sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component = 1) :
-- imply
  (∑ dart : SixVertexOrientedDisagreementDart omega eta, if sixVertexDegreeTwoSynchronizedComponentSelector homega heta hdegree component dart then sixVertexDegreeTwoStrandStepSeamSign hdegree dart else 0) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentSelector_seamSum_eq_one homega heta hdegree component hcharge


-- created on 2026-10-23
