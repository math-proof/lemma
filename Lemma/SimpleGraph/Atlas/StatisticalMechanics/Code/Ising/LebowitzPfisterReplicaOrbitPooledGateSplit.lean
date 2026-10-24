import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
open Finset StatMech StatMech.Ising


/--
[lpReplicaTwoPairRowComponent_partialReflectSource_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledGateSplit.lean)
-/
@[path]
private lemma lpReplicaTwoPairRowComponent_partialReflectSource_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {j : I}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let C := StatMech.Sharpness.RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaPartialReflectSource (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) C = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaTwoPairRowComponent_partialReflectSource_empty G sites j m K hsrc hdisc

/--
[lpReplicaRowGate_partialReflect_trueComponent_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledGateSplit.lean)
-/
@[path]
private lemma lpReplicaRowGate_partialReflect_trueComponent_general_eq
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
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let C := StatMech.Sharpness.RandomCurrent.compOf e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) A (lpReplicaPartialReflectSource B C) (lpReplicaPartialReflectTagRaw G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_partialReflect_trueComponent_general G sites m A B tag hgate

/--
[lpReplicaRowGate_pooledTargetSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledGateSplit.lean)
-/
@[path]
private lemma lpReplicaRowGate_pooledTargetSplit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let pooled := lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled let movedTag := lpReplicaPartialReflectTagRaw G sites m P tag repaired.profile = target ∧ ((lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm repaired).2.2.1 = lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L ∧ LPReplicaRowGate G sites target (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅ movedTag := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_pooledTargetSplit G sites i j m q hm tag L hgate

/--
[lpReplicaRowGate_pooledFirstSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledGateSplit.lean)
-/
@[path]
private lemma lpReplicaRowGate_pooledFirstSplit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let pooled := lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled let movedTag := lpReplicaPartialReflectTagRaw G sites m P tag let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 repaired.profile = target ∧ ((lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm repaired).2.2.1 = lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L ∧ ((LPReplicaRowGate G sites target ∅ Si movedTag ∧ (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨ (LPReplicaRowGate G sites target ∅ Sj movedTag ∧ (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T)) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_pooledFirstSplit G sites hsite hij m q hm tag L hgate

/--
[lpReplicaRowGate_pooledFirstPairSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledGateSplit.lean)
-/
@[path]
private lemma lpReplicaRowGate_pooledFirstPairSplit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let C := StatMech.Sharpness.RandomCurrent.compOf e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let pooled := lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L let repaired := lpReplicaPooledSelectedSlotMove G sites q pooled let movedTag := lpReplicaPartialReflectTagRaw G sites m P tag let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let B := Si ∆ Sj ∆ T let X := B ∩ C repaired.profile = target ∧ ((lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm repaired).2.2.1 = lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L ∧ ((LPReplicaRowGate G sites target ∅ Si movedTag ∧ Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨ (LPReplicaRowGate G sites target ∅ Sj movedTag ∧ Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding)) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_pooledFirstPairSplit G sites hsite hij m q hm tag L hgate


-- created on 2026-10-23
