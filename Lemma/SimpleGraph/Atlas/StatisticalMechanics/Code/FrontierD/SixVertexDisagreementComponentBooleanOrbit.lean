import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentBooleanOrbit.Part2
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[sixVertexDisagreementComponentSetMask_selects_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_selects_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)}
  {edge : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta selected) edge = true ↔ ∃ component ∈ selected, (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge = component.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_selects_iff omega eta selected edge

/--
[sixVertexDisagreementComponentSetMask_selects_only_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_selects_only_disagreement_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)}
  {edge : SixVertexTorusEdge T}
-- given
  (hselected : sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta selected) edge = true) :
-- imply
  sixVertexTorusEdgeDisagrees omega eta edge := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_selects_only_disagreement omega eta selected edge hselected

/--
[sixVertexDisagreementComponentSetMask_incident_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_incident_closure_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)}
  {vertex : T.Vertex}
  {first second : Fin 4}
-- given
  (hfirst : sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta selected) (sixVertexTorusIncidentEdge T vertex first) = true)
  (hsecond : sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusIncidentEdge T vertex second)) :
-- imply
  sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta selected) (sixVertexTorusIncidentEdge T vertex second) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_incident_closure omega eta selected vertex first second hfirst hsecond

/--
[sixVertexDisagreementComponentSetMask_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_full_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)} :
-- imply
  SixVertexFullDisagreementMask omega eta (sixVertexDisagreementComponentSetMask omega eta selected) := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_full omega eta selected

/--
[sixVertexDisagreementComponent_mem_iff_mask_selects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponent_mem_iff_mask_selects_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)}
  {component : SixVertexDisagreementComponent omega eta}
  {edge : SixVertexTorusEdge T}
-- given
  (hcomponent : (sixVertexTorusDisagreementGraph omega eta).connectedComponentMk edge = component.1) :
-- imply
  component ∈ selected ↔ sixVertexTorusMaskSelects (sixVertexDisagreementComponentSetMask omega eta selected) edge = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponent_mem_iff_mask_selects omega eta selected component edge hcomponent

/--
[sixVertexDisagreementComponentSetMask_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  Function.Injective (sixVertexDisagreementComponentSetMask omega eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_injective omega eta

/--
[sixVertexDisagreementComponentSetMask_seamTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_seamTransfer_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)} :
-- imply
  sixVertexTorusMaskSeamTransfer (sixVertexDisagreementComponentSetMask omega eta selected) omega eta = ∑ component ∈ selected, sixVertexDisagreementComponentCharge omega eta component := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_seamTransfer omega eta selected

/--
[sixVertexDisagreementComponentSetMask_seamTransfer_of_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma sixVertexDisagreementComponentSetMask_seamTransfer_of_unit_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {selected : Finset (SixVertexDisagreementComponent omega eta)}
-- given
  (hunit : forall component : SixVertexDisagreementComponent omega eta, sixVertexDisagreementComponentCharge omega eta component = 1) :
-- imply
  sixVertexTorusMaskSeamTransfer (sixVertexDisagreementComponentSetMask omega eta selected) omega eta = selected.card := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementComponentSetMask_seamTransfer_of_unit omega eta hunit selected

/--
[SixVertexFullDisagreementMask.of_pairSwitch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma of_pairSwitch_eq
  {T : EvenTorus}
  {omega eta firstMask secondMask : SixVertexArrows T}
-- given
  (hfirst : SixVertexFullDisagreementMask omega eta firstMask) :
-- imply
  SixVertexFullDisagreementMask (sixVertexTorusSwitchFirst secondMask omega eta) (sixVertexTorusSwitchSecond secondMask omega eta) firstMask := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.of_pairSwitch hfirst

/--
[SixVertexFullDisagreementMask.switchFirst_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma switchFirst_ice_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask)
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  (sixVertexTorusSwitchFirst mask omega eta).IceRule := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.switchFirst_ice hmask homega heta

/--
[SixVertexFullDisagreementMask.switchSecond_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementComponentBooleanOrbit.lean)
-/
@[path]
private lemma switchSecond_ice_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask)
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  (sixVertexTorusSwitchSecond mask omega eta).IceRule := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.switchSecond_ice hmask homega heta


-- created on 2026-10-23
