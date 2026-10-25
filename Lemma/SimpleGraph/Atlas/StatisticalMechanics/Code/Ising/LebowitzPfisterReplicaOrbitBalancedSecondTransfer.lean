import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part3
open Finset StatMech StatMech.Ising


/--
[lpReplica_source_symmDiff_partialReflectSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplica_source_symmDiff_partialReflectSource_eq
  [Fintype V]
  [DecidableEq V]
  {A C : Finset (LPReplicaCurrentVertex V)} :
-- imply
  A ∆ lpReplicaPartialReflectSource A C = (A ∩ C) ∆ (A ∩ C).map lpReplicaCurrentReflect.toEmbedding := by
-- proof
  apply StatMech.Ising.lpReplica_source_symmDiff_partialReflectSource A C

/--
[lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let C := StatMech.Sharpness.RandomCurrent.compOf (endsM (lpReplicaCurrentGraph G sites) m) K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let X := (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) ∩ C let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 ((Si ∆ Sj ∆ T) ∆ Si = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨ ((Si ∆ Sj ∆ T) ∆ Sj = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagRowComponent_missingSource_eq_half_reflect G sites hsite hij m K hsrc hdisc

/--
[exists_lpReplicaOffdiag_missingSource_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma exists_lpReplicaOffdiag_missingSource_half_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {K : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : StatMech.Sharpness.RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) K = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) K lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (∃ X, Sj ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) ∨ (∃ X, Si ∆ T = X ∆ X.map lpReplicaCurrentReflect.toEmbedding) := by
-- proof
  apply StatMech.Ising.exists_lpReplicaOffdiag_missingSource_half G sites hsite hij m K hsrc hdisc

/--
[lpReplicaPartialReflectTagRaw_toggleRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaPartialReflectTagRaw_toggleRows_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaPartialReflectTagRaw G sites m P (lpReplicaToggleRows G sites m P tag) = lpReplicaToggleRows G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectCopiesRaw G sites m P P) (lpReplicaPartialReflectTagRaw G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectTagRaw_toggleRows G sites m P tag

/--
[lpReplicaRowComponent_currentTrue_sources_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaRowComponent_currentTrue_sources_empty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {row : Bool}
  {root : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m A B tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag row let P := edgeComponent e K root StatMech.Sharpness.RandomCurrent.sources e (P.filter fun c => (tag c).2 = true) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaRowComponent_currentTrue_sources_empty G sites m A B tag hgate row root

/--
[lpReplicaBalancedComponentSelector_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentSelector_filter_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K0 := lpReplicaRowCopies G sites m tag false let K1 := lpReplicaRowCopies G sites m tag true let C0 := edgeComponent e K0 (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) let C1 := edgeComponent e K1 (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) (lpReplicaBalancedComponentSelector G sites m tag).filter (fun c => (tag c).2 = current) = (lpReplicaCurrentCopies G sites m tag false current ∩ C0) ∪ (lpReplicaCurrentCopies G sites m tag true current ∩ C1) := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentSelector_filter G sites m tag current

/--
[lpReplicaBalancedComponentSelector_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentSelector_sources_eq
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
  let e := endsM (lpReplicaCurrentGraph G sites) m let K0 := lpReplicaRowCopies G sites m tag false let C0 := StatMech.Sharpness.RandomCurrent.compOf e K0 (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) StatMech.Sharpness.RandomCurrent.sources e ((lpReplicaBalancedComponentSelector G sites m tag).filter fun c => (tag c).2 = false) = B ∩ C0 ∧ StatMech.Sharpness.RandomCurrent.sources e ((lpReplicaBalancedComponentSelector G sites m tag).filter fun c => (tag c).2 = true) = ∅ := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentSelector_sources G sites m B tag hgate

/--
[lpReplicaBalancedComponentSelector_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaBalancedComponentSelector_disconnects_eq
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
  let moved := lpReplicaToggleRows G sites m (lpReplicaBalancedComponentSelector G sites m tag) tag (¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m moved false) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) ∧ ¬ StatMech.Sharpness.RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (lpReplicaRowCopies G sites m moved true) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaBalancedComponentSelector_disconnects G sites m B tag hgate

/--
[lpReplica_map_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplica_map_symmDiff_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq X]
  [DecidableEq Y]
  {f : X ↪ Y}
  {A B : Finset X} :
-- imply
  (A ∆ B).map f = A.map f ∆ B.map f := by
-- proof
  apply StatMech.Ising.lpReplica_map_symmDiff f A B

/--
[lpReplicaCurrentReflect_seam_symmDiff_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitBalancedSecondTransfer.lean)
-/
@[path]
private lemma lpReplicaCurrentReflect_seam_symmDiff_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i : I}
-- given
  (sites : I -> V) :
-- imply
  (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1).map lpReplicaCurrentReflect.toEmbedding = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentReflect_seam_symmDiff_ghost G sites i


-- created on 2026-10-23
