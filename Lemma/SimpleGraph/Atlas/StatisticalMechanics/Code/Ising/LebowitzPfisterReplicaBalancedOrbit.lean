import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaBalancedOrbit
open Finset StatMech StatMech.Ising


/--
[lpReplicaRowCopies_partialReflectTagRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowCopies_partialReflectTagRaw_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectTagRaw G sites m P tag) row = lpReplicaPartialReflectCopiesRaw G sites m P (lpReplicaRowCopies G sites m tag row) := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_partialReflectTagRaw G sites m P tag row

/--
[lpReplicaCurrentCopies_partialReflectTagRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_partialReflectTagRaw_eq
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
  lpReplicaCurrentCopies G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) (lpReplicaPartialReflectTagRaw G sites m P tag) row current = lpReplicaPartialReflectCopiesRaw G sites m P (lpReplicaCurrentCopies G sites m tag row current) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_partialReflectTagRaw G sites m P tag row current

/--
[lpReplicaPartialReflectCopiesRaw_connK_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_connK_of_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {a b : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hTP : Disjoint T P) :
-- imply
  RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P T) a b <-> RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) T a b := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_connK_of_disjoint G sites m P T hTP a b

/--
[lpReplicaPartialReflectCopiesRaw_sources_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaPartialReflectCopiesRaw_sources_of_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P T : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hTP : Disjoint T P) :
-- imply
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P))) (lpReplicaPartialReflectCopiesRaw G sites m P T) = RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) T := by
-- proof
  apply StatMech.Ising.lpReplicaPartialReflectCopiesRaw_sources_of_disjoint G sites m P T hTP

/--
[lpReplicaRowGate_partialReflect_trueComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_partialReflect_trueComponent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ B tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let C := RandomCurrent.compOf e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) ∅ (lpReplicaPartialReflectSource B C) (lpReplicaPartialReflectTagRaw G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_partialReflect_trueComponent G sites m B tag hgate

/--
[lpReplicaRowGate_partialReflect_offdiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_partialReflect_offdiag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (LPReplicaRowGate G sites target ∅ Si (lpReplicaPartialReflectTagRaw G sites m P tag) ∧ (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨ (LPReplicaRowGate G sites target ∅ Sj (lpReplicaPartialReflectTagRaw G sites m P tag) ∧ (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_partialReflect_offdiag G sites hsite hij m tag hgate

/--
[lpReplicaSwapRowsTag_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaSwapRowsTag_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaSwapRowsTag (G := G) (sites := sites) (m := m)) := by
-- proof
  apply StatMech.Ising.lpReplicaSwapRowsTag_involutive G sites m

/--
[lpReplicaCurrentCopies_swapRowsTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaCurrentCopies_swapRowsTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row current : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaCurrentCopies G sites m (lpReplicaSwapRowsTag tag) row current = lpReplicaCurrentCopies G sites m tag (!row) current := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentCopies_swapRowsTag G sites m tag row current

/--
[lpReplicaRowCopies_swapRowsTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowCopies_swapRowsTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {row : Bool}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaRowCopies G sites m (lpReplicaSwapRowsTag tag) row = lpReplicaRowCopies G sites m tag (!row) := by
-- proof
  apply StatMech.Ising.lpReplicaRowCopies_swapRowsTag G sites m tag row

/--
[lpReplicaRowGate_swapRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_swapRows_eq
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
  LPReplicaRowGate G sites m B A (lpReplicaSwapRowsTag tag) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_swapRows G sites m A B tag hgate

/--
[lpReplicaRowGate_fullSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_fullSources_eq
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
  RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) = A ∆ B := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_fullSources G sites m A B tag hgate

/--
[lpReplicaRowGate_totalSources_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_totalSources_unique_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B C D : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag₁ tag₂ : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (h₁ : LPReplicaRowGate G sites m A B tag₁)
  (h₂ : LPReplicaRowGate G sites m C D tag₂) :
-- imply
  A ∆ B = C ∆ D := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_totalSources_unique G sites m A B C D tag₁ tag₂ h₁ h₂

/--
[lpReplicaRowGate_intermediate_ne_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_intermediate_ne_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag₁ tag₂ : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hmid : LPReplicaRowGate G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) ∅ tag₁)
  (htarget : LPReplicaRowGate G sites m (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i) (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag₂) :
-- imply
  False := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_intermediate_ne_target G sites i j m tag₁ tag₂ hmid htarget

/--
[lpReplicaRowGate_partialReflect_offdiag_swapRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaBalancedOrbit.lean)
-/
@[path]
private lemma lpReplicaRowGate_partialReflect_offdiag_swapRows_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hgate : LPReplicaRowGate G sites m ∅ (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) tag) :
-- imply
  let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let movedTag := lpReplicaSwapRowsTag (lpReplicaPartialReflectTagRaw G sites m P tag) let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (LPReplicaRowGate G sites target Si ∅ movedTag ∧ (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨ (LPReplicaRowGate G sites target Sj ∅ movedTag ∧ (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpReplicaRowGate_partialReflect_offdiag_swapRows G sites hsite hij m tag hgate


-- created on 2026-10-23
