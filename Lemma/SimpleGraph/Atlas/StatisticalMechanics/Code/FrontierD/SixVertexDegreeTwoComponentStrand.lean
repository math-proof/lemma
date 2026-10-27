import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoComponentStrand.Part2
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[SixVertexLocallyDegreeTwo.pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma pairSwitch_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  SixVertexLocallyDegreeTwo (sixVertexTorusSwitchFirst mask omega eta) (sixVertexTorusSwitchSecond mask omega eta) := by
-- proof
  apply StatMech.FrontierD.SixVertexLocallyDegreeTwo.pairSwitch hdegree

/--
[sixVertexTorusMaskSelects_maskXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexTorusMaskSelects_maskXor_eq
  {T : EvenTorus}
  {first second : SixVertexArrows T}
  {edge : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusMaskSelects (sixVertexTorusMaskXor first second) edge = (sixVertexTorusMaskSelects first edge != sixVertexTorusMaskSelects second edge) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusMaskSelects_maskXor first second edge

/--
[sixVertexDisagreementComponentSetMask_symmDiff_selects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_symmDiff_selects_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {first second : Finset (SixVertexDisagreementComponent omega eta)}
  {edge : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta (first ∆ second)) edge = (sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta first) edge != sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta second) edge) := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_symmDiff_selects omega eta first second edge

/--
[sixVertexDisagreementComponentSetMask_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_symmDiff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {first second : Finset (SixVertexDisagreementComponent omega eta)} :
-- imply
  sixVertexDisagreementComponentSetMask omega eta (first ∆ second) = sixVertexTorusMaskXor (sixVertexDisagreementComponentSetMask omega eta first) (sixVertexDisagreementComponentSetMask omega eta second) := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_symmDiff omega eta first second

/--
[sixVertexTorusSwitchFirst_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexTorusSwitchFirst_pairSwitch_eq
  {T : EvenTorus}
  {first second omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusSwitchFirst second (sixVertexTorusSwitchFirst first omega eta) (sixVertexTorusSwitchSecond first omega eta) = sixVertexTorusSwitchFirst (sixVertexTorusMaskXor first second) omega eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchFirst_pairSwitch first second omega eta

/--
[sixVertexTorusSwitchSecond_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexTorusSwitchSecond_pairSwitch_eq
  {T : EvenTorus}
  {first second omega eta : SixVertexArrows T} :
-- imply
  sixVertexTorusSwitchSecond second (sixVertexTorusSwitchFirst first omega eta) (sixVertexTorusSwitchSecond first omega eta) = sixVertexTorusSwitchSecond (sixVertexTorusMaskXor first second) omega eta := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusSwitchSecond_pairSwitch first second omega eta

/--
[SixVertexFullDisagreementMask.selects_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma selects_of_reachable_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
  {seed edge : SixVertexTorusEdge T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask)
  (hseed : sixVertexTorusMaskSelects mask seed = true)
  (hreach : (sixVertexTorusDisagreementGraph omega eta).Reachable seed edge) :
-- imply
  sixVertexTorusMaskSelects mask edge = true := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.selects_of_reachable hmask hseed hreach

/--
[sixVertexTorusIncidentEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexTorusIncidentEdge_injective_eq
  {T : EvenTorus}
  {vertex : T.Vertex} :
-- imply
  Function.Injective (sixVertexTorusIncidentEdge T vertex) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusIncidentEdge_injective T vertex

/--
[sixVertexDegreeTwoOrientedComponentEdge_successor_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrientedComponentEdge_successor_adj_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexTorusDisagreementGraph omega eta).Adj (sixVertexDegreeTwoOrientedComponentEdge hdegree dart) (sixVertexDegreeTwoOrientedComponentEdge hdegree (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrientedComponentEdge_successor_adj homega heta hdegree dart

/--
[sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {first second : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hsame : (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).SameCycle first second) :
-- imply
  (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk (sixVertexDegreeTwoOrientedComponentEdge hdegree first) = (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk (sixVertexDegreeTwoOrientedComponentEdge hdegree second) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoOrientedComponentEdge_eq_of_sameCycle homega heta hdegree first second hsame

/--
[sixVertexDegreeTwoStrand_mask_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrand_mask_component_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
  {edge : SixVertexTorusEdge T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hselected : sixVertexTorusMaskSelects (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask edge = true) :
-- imply
  (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge = (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrand_mask_component homega heta hdegree seed edge hselected

/--
[sixVertexDegreeTwoStrand_mask_seedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrand_mask_seedEdge_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexTorusMaskSelects (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrand_mask_seedEdge homega heta hdegree seed

/--
[sixVertexDegreeTwoStrand_mask_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrand_mask_full_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  SixVertexFullDisagreementMask omega eta (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrand_mask_full homega heta hdegree seed

/--
[sixVertexDegreeTwoStrand_mask_eq_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrand_mask_eq_component_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : SixVertexDisagreementComponent omega eta}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hseed : (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = component.1) :
-- imply
  (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask = sixVertexDisagreementComponentSetMask omega eta {component} := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrand_mask_eq_component homega heta hdegree component seed hseed

/--
[sixVertexDegreeTwoStrand_mask_eq_reference_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoComponentStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrand_mask_eq_reference_component_eq
  {T : EvenTorus}
  {omega eta referenceFirst referenceSecond : SixVertexArrows T}
  {component : SixVertexDisagreementComponent referenceFirst referenceSecond}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hgraph : sixVertexTorusDisagreementGraph omega eta = sixVertexTorusDisagreementGraph referenceFirst referenceSecond)
  (hseed : (sixVertexTorusDisagreementGraph referenceFirst referenceSecond).connectedComponentMk (sixVertexDegreeTwoOrientedComponentEdge hdegree seed) = component.1) :
-- imply
  (sixVertexDegreeTwoStrandDirectedSimpleCycle homega heta hdegree seed).mask = sixVertexDisagreementComponentSetMask referenceFirst referenceSecond {component} := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrand_mask_eq_reference_component homega heta hdegree hgraph component seed hseed


-- created on 2026-10-23
