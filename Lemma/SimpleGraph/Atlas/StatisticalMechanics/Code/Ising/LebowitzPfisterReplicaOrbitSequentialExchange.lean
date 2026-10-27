import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
open Finset StatMech StatMech.Ising


/--
[lpReplicaBalancedComponentSelector_sources_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentSelector_sources_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m StatMech.Sharpness.RandomCurrent.sources e ((lpReplicaBalancedComponentSelector G sites m tag).filter fun c => (tag c).2 = false) = lpReplicaBalancedComponentBoundary G sites m A B tag ∧ StatMech.Sharpness.RandomCurrent.sources e ((lpReplicaBalancedComponentSelector G sites m tag).filter fun c => (tag c).2 = true) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentSelector_sources_general G sites m A B tag hgate

/--
[lpReplicaBalancedComponentSelector_rowCurrentSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentSelector_rowCurrentSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m B ∅ tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let P := lpReplicaBalancedComponentSelector G sites m tag let X := lpReplicaBalancedComponentBoundary G sites m B ∅ tag StatMech.Sharpness.RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag false false ∩ P) = X ∧ StatMech.Sharpness.RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag true false ∩ P) = ∅ ∧ StatMech.Sharpness.RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag false true ∩ P) = ∅ ∧ StatMech.Sharpness.RandomCurrent.sources e (lpReplicaCurrentCopies G sites m tag true true ∩ P) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentSelector_rowCurrentSources G sites m B tag hgate

/--
[lpReplicaBalancedComponentSelector_disconnects_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentSelector_disconnects_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  let moved := lpReplicaToggleRows G sites m (lpReplicaBalancedComponentSelector G sites m tag) tag (¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m moved false) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧ ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m moved true) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentSelector_disconnects_general G sites m A B tag hgate

/--
[lpReplicaRowGate_balancedComponentExchange_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaRowGate_balancedComponentExchange_general_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  let D := lpReplicaBalancedComponentBoundary G sites m A B tag LPReplicaRowGate G sites m (A ∆ D) (B ∆ D) (lpReplicaToggleRows G sites m (lpReplicaBalancedComponentSelector G sites m tag) tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_balancedComponentExchange_general G sites m A B tag hgate

/--
[lpReplicaCoupledReflectToggle_currentSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaCoupledReflectToggle_currentSources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let T := lpReplicaCurrentCopies G sites m tag row current let U := lpReplicaCurrentCopies G sites m tag (!row) current StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) target) (lpReplicaCurrentCopies G sites target (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) row current) = (StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) T ∆ StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (T ∩ P)) ∆ (StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (U ∩ P)).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplicaCoupledReflectToggle_currentSources G sites m P tag row current

/--
[lpReplicaCurrentReflect_map_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_map_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {X : Finset (LPReplicaCurrentVertex V)} :
-- imply
  (X.map lpReplicaCurrentReflect.toEmbedding).map lpReplicaCurrentReflect.toEmbedding = X := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_map_involutive X

/--
[lpReplicaRowGate_coupledReflectToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaRowGate_coupledReflectToggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {A B X0 X1 Z0 Z1 : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag)
  (hfalse0 : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag false false ∩ P) = X0)
  (hfalse1 : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag true false ∩ P) = X1)
  (htrue0 : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag false true ∩ P) = Z0)
  (htrue1 : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag true true ∩ P) = Z1)
  (htruePair : Z0 = Z1.map lpReplicaCurrentReflect.toEmbedding)
  (hdisc0 : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) false) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)
  (hdisc1 : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) true) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) ((A ∆ X0) ∆ X1.map lpReplicaCurrentReflect.toEmbedding) ((B ∆ X1) ∆ X0.map lpReplicaCurrentReflect.toEmbedding) (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_coupledReflectToggle G sites m P A B X0 X1 Z0 Z1 tag hgate hfalse0 hfalse1 htrue0 htrue1 htruePair hdisc0 hdisc1

/--
[LPReplicaRightCoupledPairedCut.falseSource0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma falseSource0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag false false ∩ cut.selector) = cut.half := by
-- proof
  apply StatMech.Ising.LPReplicaRightCoupledPairedCut.falseSource0 G sites m B tag cut

/--
[LPReplicaRightCoupledPairedCut.falseSource1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma falseSource1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag true false ∩ cut.selector) = cut.half := by
-- proof
  apply StatMech.Ising.LPReplicaRightCoupledPairedCut.falseSource1 G sites m B tag cut

/--
[LPReplicaRightCoupledPairedCut.trueSource0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma trueSource0_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag false true ∩ cut.selector) = cut.trueHalf := by
-- proof
  apply StatMech.Ising.LPReplicaRightCoupledPairedCut.trueSource0 G sites m B tag cut

/--
[LPReplicaRightCoupledPairedCut.trueSource1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma trueSource1_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaCurrentCopies G sites m tag true true ∩ cut.selector) = cut.trueHalf.map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.LPReplicaRightCoupledPairedCut.trueSource1 G sites m B tag cut

/--
[lpReplicaCoupledReflectToggleTagRaw_swapRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaCoupledReflectToggleTagRaw_swapRows_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCoupledReflectToggleTagRaw G sites m P (lpReplicaSwapRowsTag tag) = lpReplicaSwapRowsTag (lpReplicaCoupledReflectToggleTagRaw G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaCoupledReflectToggleTagRaw_swapRows G sites m P tag

/--
[lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaSwapRowsTag (lpReplicaCoupledReflectToggleTagRaw G sites m P (lpReplicaSwapRowsTag tag)) = lpReplicaCoupledReflectToggleTagRaw G sites m P tag := by
-- proof
  apply StatMech.Ising.lpReplicaSwapRowsTag_coupledReflectToggleTagRaw_swapRows G sites m P tag

/--
[LPReplicaCoupledPairedCut.half_eq_empty_of_row1False_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma half_eq_empty_of_row1False_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hempty : lpReplicaCurrentCopies G sites m tag true false = ∅) :
-- imply
  cut.half = ∅ := by
-- proof
  apply StatMech.Ising.LPReplicaCoupledPairedCut.half_eq_empty_of_row1False_empty G sites m B tag cut hempty

/--
[LPReplicaCoupledPairedCut.balancedComponentBoundary_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma balancedComponentBoundary_eq_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m B ∅ tag)
  (hselector : cut.selector = lpReplicaBalancedComponentSelector G sites m tag) :
-- imply
  lpReplicaBalancedComponentBoundary G sites m B ∅ tag = ∅ := by
-- proof
  apply StatMech.Ising.LPReplicaCoupledPairedCut.balancedComponentBoundary_eq_empty G sites m B tag hgate cut hselector

/--
[LPReplicaCoupledPairedCut.doubledHalf_eq_empty_of_balancedSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma doubledHalf_eq_empty_of_balancedSelector_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m B ∅ tag)
  (hselector : cut.selector = lpReplicaBalancedComponentSelector G sites m tag) :
-- imply
  cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding = ∅ := by
-- proof
  apply StatMech.Ising.LPReplicaCoupledPairedCut.doubledHalf_eq_empty_of_balancedSelector G sites m B tag hgate cut hselector

/--
[lpReplicaRowGate_coupledPairedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaRowGate_coupledPairedCut_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m B ∅ tag) :
-- imply
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)) (B ∆ D) D (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_coupledPairedCut G sites m B tag hgate cut

/--
[lpReplicaRowGate_rightCoupledPairedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaRowGate_rightCoupledPairedCut_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
  {cut : LPReplicaRightCoupledPairedCut G sites m B tag}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ B tag) :
-- imply
  let D := cut.half ∆ cut.half.map lpReplicaCurrentReflect.toEmbedding LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ cut.selector)) (profileFlux (lpReplicaCurrentGraph G sites) m cut.selector)) D (B ∆ D) (lpReplicaCoupledReflectToggleTagRaw G sites m cut.selector tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_rightCoupledPairedCut G sites m B tag hgate cut

/--
[lpReplica_half_symmDiff_reflect_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplica_half_symmDiff_reflect_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {X : Finset (LPReplicaCurrentVertex V)} :
-- imply
  (X ∆ X.map lpReplicaCurrentReflect.toEmbedding).map lpReplicaCurrentReflect.toEmbedding = X ∆ X.map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplica_half_symmDiff_reflect_fixed X

/--
[lpReplicaOrbitFourColorSlotState_canonicalPartialReflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotState_canonicalPartialReflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaOrbitFourColorSlotStateOfTag G sites q (lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m P)) ((lpReplicaSymmetrizedProfile_partialReflectCopies G sites m P).trans hm) (lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L) (lpReplicaCanonicalPartialReflectToggleTag G sites q m hm L P tag) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotState_canonicalPartialReflect G sites q m hm L P tag

/--
[lpReplicaPartialReflectCanonicalCopyEquiv_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCanonicalCopyEquiv_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {c : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  (lpReplicaPartialReflectCanonicalCopyEquiv G sites q m hm L P c).1 = if c ∈ P then lpReplicaCurrentEdgeReflect G sites c.1 else c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCanonicalCopyEquiv_edge G sites q m hm L P c

/--
[lpReplicaPartialReflectCanonicalRelabelEquiv_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitSequentialExchange.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCanonicalRelabelEquiv_ends_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {d : Copy (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  endsM (lpReplicaCurrentGraph G sites) (lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectCanonicalRelabelEquiv G sites q m hm L P d) = endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) d := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCanonicalRelabelEquiv_ends G sites q m hm L P d


-- created on 2026-10-23
