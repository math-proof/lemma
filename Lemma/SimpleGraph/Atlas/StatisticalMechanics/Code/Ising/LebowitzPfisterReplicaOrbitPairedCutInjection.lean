import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part12
open Finset StatMech StatMech.Ising


/--
[lpReplicaOrientedFourColorSlotState_ofRowGate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorSlotState_ofRowGate_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomOfRowGate G sites m q tag A B hm hgate L)) = lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorSlotState_ofRowGate G sites A B q m tag hm hgate L

/--
[lpReplicaOrbitFourColorSlotStateOfTag_cast_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotStateOfTag_cast_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : n = m)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hn : lpReplicaSymmetrizedProfile G sites n = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaOrbitFourColorSlotStateOfTag G sites q n hn (cast (congrArg (LPReplicaProfileOrbitLabel G sites q) h.symm) L) (fun c => tag (cast (congrArg (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites)) h) c)) = lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotStateOfTag_cast_profile G sites q m n h hm hn L tag

/--
[lpReplicaPartialReflectTransportTag_cast_eq_coupledRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaPartialReflectTransportTag_cast_eq_coupledRaw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {d : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P))}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaPartialReflectTransportTag G sites m P tag (cast (congrArg (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites)) (lpReplicaCollisionProfile_compl_eq_partialReflectProfile G sites m P)) d) = lpReplicaCoupledReflectToggleTagRaw G sites m P tag d := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectTransportTag_cast_eq_coupledRaw G sites m P tag d

/--
[lpReplicaOrbitFourColorSlotState_partialReflect_of_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotState_partialReflect_of_compatible_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hcompat : LPReplicaPartialReflectCommonSlotCompatible G sites q m hm L P) :
-- imply
  lpReplicaOrbitFourColorSlotStateOfTag G sites q (lpReplicaPartialReflectProfile G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P)) ((lpReplicaSymmetrizedProfile_partialReflectCopies G sites m P).trans hm) (lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L) (lpReplicaPartialReflectTransportTag G sites m P tag) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotState_partialReflect_of_compatible G sites q m hm L P tag hcompat

/--
[lpReplicaOrientedFourColorSlotState_cast_targetBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorSlotState_cast_targetBoundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A D E : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaDecoratedOrbitAtom G sites A D q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : D = E) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites A E q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A E q (cast (congrArg (fun Z => LPReplicaDecoratedOrbitAtom G sites A Z q) h) x)) = lpReplicaOrientedFourColorSlotState G sites A D q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A D q x) := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorSlotState_cast_targetBoundary G sites A D E q h x

/--
[lpReplicaOrientedFourColorSlotState_cast_sourceBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorSlotState_cast_sourceBoundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A C D : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaDecoratedOrbitAtom G sites A D q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (h : A = C) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites C D q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites C D q (cast (congrArg (fun Z => LPReplicaDecoratedOrbitAtom G sites Z D q) h) x)) = lpReplicaOrientedFourColorSlotState G sites A D q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A D q x) := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorSlotState_cast_sourceBoundary G sites A C D q h x

/--
[lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (horbit : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m B ∅ tag) :
-- imply
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding lpReplicaOrientedFourColorSlotState G sites (B ∆ D) D q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites (B ∆ D) D q (lpReplicaDecoratedOrbitAtomOfCoupledPairedCut G sites m q B tag horbit hgate L cut)) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m horbit L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m horbit L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfCoupledPairedCut_slotState G sites m q B tag horbit hgate L cut

/--
[lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (horbit : lpReplicaSymmetrizedProfile G sites m = q)
  (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
  (hgate : LPReplicaRowGate G sites m ∅ B tag) :
-- imply
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding lpReplicaOrientedFourColorSlotState G sites D (B ∆ D) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites D (B ∆ D) q (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut G sites m q B tag horbit hB hgate L cut)) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m horbit L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m horbit L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCut_slotState G sites m q B tag horbit hB hgate L cut

/--
[lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B A Dtarget : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (horbit : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m B ∅ tag)
  (hA : B ∆ (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) = A)
  (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = Dtarget) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites A Dtarget q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A Dtarget q (lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast G sites m q B A Dtarget tag horbit hgate L cut hA hD)) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m horbit L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m horbit L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfCoupledPairedCutCast_slotState G sites m q B A Dtarget tag horbit hgate L cut hA hD

/--
[lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B A Dtarget : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (horbit : lpReplicaSymmetrizedProfile G sites m = q)
  (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
  (hgate : LPReplicaRowGate G sites m ∅ B tag)
  (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = A)
  (hD : B ∆ (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) = Dtarget) :
-- imply
  lpReplicaOrientedFourColorSlotState G sites A Dtarget q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A Dtarget q (lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast G sites m q B A Dtarget tag horbit hB hgate L cut hA hD)) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m horbit L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m horbit L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomOfRightCoupledPairedCutCast_slotState G sites m q B A Dtarget tag horbit hB hgate L cut hA hD

/--
[lpReplica_even_card_half_symmDiff_reflect_inter_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplica_even_card_half_symmDiff_reflect_inter_leftSide_eq
  [Fintype V]
  [DecidableEq V]
  {X : Finset (LPReplicaCurrentVertex V)}
-- given
  (hX : Even X.card) :
-- imply
  Even ((X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∩ lpReplicaCurrentLeftSide).card := by
-- proof
  apply StatMech.Ising.lpReplica_even_card_half_symmDiff_reflect_inter_leftSide X hX

/--
[LPReplicaEvenLeftBoundary.symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  {X Y : Finset (LPReplicaCurrentVertex V)}
-- given
  (hX : LPReplicaEvenLeftBoundary X)
  (hY : LPReplicaEvenLeftBoundary Y) :
-- imply
  LPReplicaEvenLeftBoundary (X ∆ Y) := by
-- proof
  apply StatMech.Ising.LPReplicaEvenLeftBoundary.symmDiff hX hY

/--
[lpReplica_doubledBoundary_evenLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplica_doubledBoundary_evenLeft_eq
  [Fintype V]
  [DecidableEq V]
  {X : Finset (LPReplicaCurrentVertex V)}
-- given
  (hX : Even X.card) :
-- imply
  LPReplicaEvenLeftBoundary (X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplica_doubledBoundary_evenLeft X hX

/--
[lpReplica_evenLeft_after_doubledBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplica_evenLeft_after_doubledBoundary_eq
  [Fintype V]
  [DecidableEq V]
  {A X : Finset (LPReplicaCurrentVertex V)}
-- given
  (hA : LPReplicaEvenLeftBoundary A)
  (hX : Even X.card) :
-- imply
  LPReplicaEvenLeftBoundary (A ∆ (X ∆ X.map lpReplicaCurrentReflect.toEmbedding)) := by
-- proof
  apply StatMech.Ising.lpReplica_evenLeft_after_doubledBoundary A X hA hX

/--
[lpReplica_doubledThenSeam_targetBoundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplica_doubledThenSeam_targetBoundaries_eq
  [Fintype V]
  [DecidableEq V]
  {Si Sj T Sk D : Finset (LPReplicaCurrentVertex V)}
-- given
  (hD : D = Si ∆ Sk) :
-- imply
  D ∆ Sk = Si ∧ ((Si ∆ Sj ∆ T) ∆ D) ∆ Sk = Sj ∆ T := by
-- proof
  apply StatMech.Ising.lpReplica_doubledThenSeam_targetBoundaries Si Sj T Sk D hD

/--
[lpReplicaBalancedComponentBoundary_ne_seam_symmDiff_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentBoundary_ne_seam_symmDiff_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {i : I}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m B ∅ tag) :
-- imply
  lpReplicaBalancedComponentBoundary G sites m B ∅ tag ≠ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentBoundary_ne_seam_symmDiff_ghost G sites m B tag hgate i

/--
[lpReplicaRowGate_rightPairedCut_thenSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaRowGate_rightPairedCut_thenSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Si Sj T Sk : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m (Si ∆ Sj ∆ T) tag}
  {Q : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)))}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ (Si ∆ Sj ∆ T) tag)
  (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = Si ∆ Sk)
  (hfalse : StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))) (Q.filter fun c => ((lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) c).2 = false) = Sk)
  (htrue : StatMech.Sharpness.RandomCurrent.sources (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))) (Q.filter fun c => ((lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) c).2 = true) = ∅)
  (hdisc0 : ¬ StatMech.Sharpness.RandomCurrent.connK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))) (lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)) (lpReplicaToggleRows G sites _ Q (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag)) false) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  (hdisc1 : ¬ StatMech.Sharpness.RandomCurrent.connK (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector))) (lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)) (lpReplicaToggleRows G sites _ Q (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag)) true) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)) Si (Sj ∆ T) (lpReplicaToggleRows G sites _ Q (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag)) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_rightPairedCut_thenSeam G sites m Si Sj T Sk tag hgate cut hD Q hfalse htrue hdisc0 hdisc1

/--
[LPReplicaRightCoupledPairedCut.half_card_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma half_card_even_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  Even cut.half.card := by
-- proof
  apply StatMech.Ising.LPReplicaRightCoupledPairedCut.half_card_even G sites m B tag cut

/--
[LPReplicaRightCoupledPairedCut.doubledHalf_ne_seamSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma doubledHalf_ne_seamSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
  {i : I}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding ≠ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i := by
-- proof
  apply StatMech.Ising.LPReplicaRightCoupledPairedCut.doubledHalf_ne_seamSource G sites m B tag cut i

/--
[lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  let B := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let hfixed : B.map lpReplicaCurrentReflect.toEmbedding = B := by simpa only [B] using lpReplicaCurrentReflect_offdiagSource G sites i j let d := lpReplicaDecoratedOrbitAtomFixedRowGateData G sites ∅ B q hfixed z lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z = lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1 z.1.1.2 z.2.2 d.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceSlotState_fixedRowGateData G sites i j q z

/--
[lpReplicaOrbitCanonicalFirstSlot_ne_secondSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitCanonicalFirstSlot_ne_secondSlot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
-- imply
  lpReplicaOrbitCanonicalFirstSlot G sites q hcard ≠ lpReplicaOrbitCanonicalSecondSlot G sites q hcard := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCanonicalFirstSlot_ne_secondSlot G sites q hcard

/--
[lpReplicaOrbitCanonicalFirstTwoSlots_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitCanonicalFirstTwoSlots_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
-- imply
  (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCanonicalFirstTwoSlots_card G sites q hcard

/--
[lpReplicaOrbitCommonSlotOrderKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitCommonSlotOrderKey_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaOrbitCommonSlotOrderKey G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCommonSlotOrderKey_injective G sites q

/--
[lpReplicaOrbitCanonicalPenultimateSlot_ne_lastSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitCanonicalPenultimateSlot_ne_lastSlot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
-- imply
  lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard ≠ lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCanonicalPenultimateSlot_ne_lastSlot G sites q hcard

/--
[lpReplicaOrbitCanonicalLastTwoSlots_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitCanonicalLastTwoSlots_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
-- imply
  (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard).card = 2 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCanonicalLastTwoSlots_card G sites q hcard

/--
[lpReplicaOrbitCanonicalLastTwoSlots_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOrbitCanonicalLastTwoSlots_terminal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
-- imply
  LPReplicaOrbitCommonSlotTerminal G sites q (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitCanonicalLastTwoSlots_terminal G sites q hcard

/--
[lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_false_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
-- imply
  ¬ LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable G sites i j q hcard z := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_false G sites i j q hcard z

/--
[lpReplicaOffdiagCoupledPairedCut_leftTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedCut_leftTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaCoupledPairedCut G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∅ tag)
  (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hA : (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∆ (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedCut_leftTarget G sites i j q m tag hm hgate L cut hD hA

/--
[lpReplicaOffdiagCoupledPairedCut_rightTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedCut_rightTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaCoupledPairedCut G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hgate : LPReplicaRowGate G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∅ tag)
  (hD : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hA : (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∆ (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedCut_rightTarget G sites i j q m tag hm hgate L cut hD hA

/--
[lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
  (hrealize : LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable G sites i j q hcard z) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCanonicalLastTwoPairedCutRealizable_target G sites i j q hcard z hrealize

/--
[lpReplicaOffdiagRightCoupledPairedCut_leftTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagRightCoupledPairedCut_leftTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
  (hgate : LPReplicaRowGate G sites m ∅ B tag)
  (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
  (hD : B ∆ (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRightCoupledPairedCut_leftTarget G sites i j q m B tag hm hB hgate L cut hA hD

/--
[lpReplicaOffdiagRightCoupledPairedCut_rightTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagRightCoupledPairedCut_rightTarget_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {B : Finset (LPReplicaCurrentVertex V)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hB : B.map lpReplicaCurrentReflect.toEmbedding = B)
  (hgate : LPReplicaRowGate G sites m ∅ B tag)
  (hA : cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
  (hD : B ∆ (cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L cut.selector) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRightCoupledPairedCut_rightTarget G sites i j q m B tag hm hB hgate L cut hA hD

/--
[lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
  (hrealize : LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable G sites i j q hcard z) :
-- imply
  ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable_target G sites i j q hcard z hrealize

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoRightPairedCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoRightPairedCuts_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
  (hcuts : forall z : LPReplicaOffdiagDecoratedSource G sites i j q, LPReplicaOffdiagCanonicalLastTwoRightPairedCutRealizable G sites i j q hcard z) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_canonicalLastTwoRightPairedCuts G sites i j q hcard hcuts

/--
[LPReplicaOffdiagCoupledPairedCrossToggleInjection.output_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma output_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCoupledPairedCrossToggleInjection G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective s.output := by
-- proof
  apply StatMech.Ising.LPReplicaOffdiagCoupledPairedCrossToggleInjection.output_injective G sites i j q s

/--
[lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCoupledPairedCrossToggleInjection G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputCard_of_crossToggleInjection G sites i j q s

/--
[lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q, ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q P (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputCard_of_fixedMaskRealizations G sites i j q P hrealize

/--
[lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalFirstTwoRealizations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalFirstTwoRealizations_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
  (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q, ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCanonicalFirstTwoSlots G sites q hcard) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalFirstTwoRealizations G sites i j q hcard hrealize

/--
[lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
  (hrealize : forall z : LPReplicaOffdiagDecoratedSource G sites i j q, ∃ y : LPReplicaOffdiagDecoratedTarget G sites i j q, LPReplicaOffdiagCoupledPairedOutput G sites i j q y ∧ (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q y).2 = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCanonicalLastTwoSlots G sites q hcard) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoRealizations G sites i j q hcard hrealize

/--
[lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoPairedCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoPairedCuts_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q))
  (hcuts : forall z : LPReplicaOffdiagDecoratedSource G sites i j q, LPReplicaOffdiagCanonicalLastTwoPairedCutRealizable G sites i j q hcard z) :
-- imply
  Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedOutputCard_of_canonicalLastTwoPairedCuts G sites i j q hcard hcuts

/--
[lpReplicaOffdiagCoupledPairedHall_of_crossToggleInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedHall_of_crossToggleInjection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCoupledPairedCrossToggleInjection G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagCoupledPairedHall G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedHall_of_crossToggleInjection G sites i j q s

/--
[lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedCrossToggleInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean)
-/
@[path]
private lemma lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedCrossToggleInjection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {s : LPReplicaOffdiagCoupledPairedCrossToggleInjection G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagOrbitAtomCardInequality_of_coupledPairedCrossToggleInjection G sites i j q s


-- created on 2026-10-23
