import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
open StatMech StatMech.FrontierD


/--
[finitePerm_function_invariant_of_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma finitePerm_function_invariant_of_firstReturn_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {f : A → B}
-- given
  (selected : A → Prop)
  (hreturn : ∀ x : {a : A // selected a}, f (finiteFirstReturn sigma selected x) = f x.1)
  (hinactive : ∀ x : A, ¬ selected x → f (sigma x) = f x) :
-- imply
  ∀ x : A, f (sigma x) = f x := by
-- proof
  apply StatMech.FrontierD.finitePerm_function_invariant_of_firstReturn sigma selected f hreturn hinactive

/--
[finitePerm_function_invariant_of_firstReturn_of_inactive_arrival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma finitePerm_function_invariant_of_firstReturn_of_inactive_arrival_eq
  [Fintype A]
  [DecidableEq A]
  {sigma : Equiv.Perm A}
  [DecidablePred selected]
  {f : A → B}
-- given
  (selected : A → Prop)
  (hreturn : ∀ x : {a : A // selected a}, f (finiteFirstReturn sigma selected x) = f x.1)
  (hinactiveArrival : ∀ x : A, ¬ selected (sigma x) → f (sigma x) = f x) :
-- imply
  ∀ x : A, f (sigma x) = f x := by
-- proof
  apply StatMech.FrontierD.finitePerm_function_invariant_of_firstReturn_of_inactive_arrival sigma selected f hreturn hinactiveArrival

/--
[sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree component (doubledAlignedVertex x) = sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree component (x.1, false) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransitionVertex_active homega heta hdegree component x

/--
[sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransitionVertex homega heta hdegree component (doubledAlignedVertex x) = sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree component x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransitionVertex_eq_branch homega heta hdegree component x

/--
[sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex homega heta hdegree component (doubledAlignedVertex x) = (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x && ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentInternalMismatchVertex_active homega heta hdegree component x

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer (doubledAlignedVertex x) = (sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree component x != (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x && ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_active homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer v = false := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask_inactive homega heta hdegree component layer v hzero

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let retie := orientedDartAlignedRetie homega heta hdegree x.1 let sourcePairing := if layer then retie.pairingQ else retie.pairingP sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer (doubledAlignedVertex x) = if sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer (doubledAlignedVertex x) then !sourcePairing else sourcePairing := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_active homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer v = alignedRoutingLoopPairing homega heta hdegree layer v := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_inactive homega heta hdegree component layer v hzero

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_recover_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkMedialTogglePairingMask (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer) = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing_recover homega heta hdegree component layer

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) = (fkColoredParityMaskStrandSlotSwap (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer) false).trans ((fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer)).trans (fkColoredParityMaskStrandSlotSwap (sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer) true)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalTargetBoundary homega heta hdegree component layer

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
-- imply
  let mask := sixVertexDegreeTwoSynchronizedComponentPhysicalRetieMask homega heta hdegree component layer let swapped := fkMedialBlackDartMaskSwap mask dart (finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 = (finiteFirstReturn (alignedBoundaryPerm homega heta hdegree layer) (activeBlackDart (omega := omega) (eta := eta)) ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_active homega heta hdegree component layer dart hactive

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState homega heta hdegree component layer x) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState_color homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta hdegree component layer x) = sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_inputState homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (sixVertexDegreeTwoSynchronizedComponentPhysicalOutputState homega heta hdegree component layer x) = sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_outputState homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_tauAdjusted homega heta hdegree component x

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (sixVertexDegreeTwoSynchronizedComponentPhysicalSourceReturnState homega heta hdegree component layer x) = sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_sourceReturnState homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta hdegree component layer x) = sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (doubledAlignedFirstReturnPerm homega heta hdegree (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta hdegree component layer x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState_bne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState_bne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta hdegree component layer x) != sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x) = sixVertexDegreeTwoSynchronizedComponentTransitionBit homega heta hdegree component (doubledAlignedFirstReturnPerm homega heta hdegree (sixVertexDegreeTwoSynchronizedComponentPhysicalInputState homega heta hdegree component layer x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentDoubledSelector_returnState_bne homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) ((finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1) = (doubledAlignedVertex (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta hdegree component layer x), doubledAlignedSlot homega heta hdegree layer (sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState homega heta hdegree component layer x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot homega heta hdegree component layer x dart hactive hslot

/--
[sixVertexDegreeTwoSynchronizedComponent_mem_states_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponent_mem_states_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  x ∈ sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component ↔ sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponent_mem_states_iff homega heta hdegree component x

/--
[sixVertexDegreeTwoSynchronizedComponent_states_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponent_states_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component).Nodup := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponent_states_nodup homega heta hdegree component

/--
[sixVertexDegreeTwoSynchronizedComponent_branchSwap_mem_states_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponent_branchSwap_mem_states_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  doubledAlignedBranchSwap x ∈ sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component ↔ x ∈ sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponent_branchSwap_mem_states_iff homega heta hdegree component x

/--
[sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  Function.Injective (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree component layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega heta hdegree component layer

/--
[sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_self_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {slot : FKLayeredStrandSlot T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component slot) = slot := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_self homega heta hdegree component slot

/--
[sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∃ i, sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree component layer i = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) ↔ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_exists_iff homega heta hdegree component layer dart

/--
[sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component)) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply homega heta hdegree component layer dart hdart

/--
[sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component)) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv_apply_of_not_mem homega heta hdegree component layer dart hdart

/--
[sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoSynchronizedComponentStates homega heta hdegree component) then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart homega heta hdegree component layer dart

/--
[sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) dart) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransportedColor_dart_of_inactive homega heta hdegree component layer dart hinactive

/--
[sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (alignedBoundaryPerm homega heta hdegree false dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransportedColor_falseBoundary_of_inactive homega heta hdegree component layer dart hinactive

/--
[sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hdart : ¬ activeBlackDart (omega := omega) (eta := eta) dart)
  (hnext : ¬ activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart)) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta hdegree component layer dart = alignedBoundaryPerm homega heta hdegree false dart := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart_of_inactive homega heta hdegree component layer dart hdart hnext

/--
[sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta hdegree component layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTargetBoundary_slotOfFalseDart homega heta hdegree component layer dart

/--
[sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T), fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta hdegree component layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component) (Fintype.card (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta hdegree component)) (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree component) (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega heta hdegree component) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_falseDart homega heta hdegree component hfalseDart

/--
[sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T), activeBlackDart (omega := omega) (eta := eta) dart ∨ activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart) → fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart homega heta hdegree component layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component) (Fintype.card (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta hdegree component)) (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree component) (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega heta hdegree component) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active homega heta hdegree component hactive

/--
[sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor homega heta hdegree component layer x = if sixVertexDegreeTwoSynchronizedComponentDoubledSelector homega heta hdegree component x then sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) x else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq homega heta hdegree component layer x

/--
[sixVertexDegreeTwoSynchronizedComponentTransportedColor_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentTransportedColor_firstReturn_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hreturn : SixVertexDegreeTwoSynchronizedComponentActiveReturnColorInvariant homega heta hdegree component)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  let arrival := (finiteFirstReturn (fkMedialBlackBoundaryPerm (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) arrival)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta hdegree component (layer, fkColoredBlackDartStrandSlotEquiv (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta hdegree component layer) dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentTransportedColor_firstReturn homega heta hdegree component hreturn layer x dart hactive hslot


-- created on 2026-10-23
