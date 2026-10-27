import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
open Finset StatMech StatMech.Ising


/--
[mem_lpReplicaPartialReflectSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaComponentReflection.lean)
-/
@[path]
private lemma mem_lpReplicaPartialReflectSource_eq
  [Fintype V]
  [DecidableEq V]
  {A C : Finset (LPReplicaCurrentVertex V)}
  {x : LPReplicaCurrentVertex V} :
-- imply
  x ∈ lpReplicaPartialReflectSource A C ↔ ((x ∈ A ∧ x ∉ C) ∧ ¬ (lpReplicaCurrentReflect x ∈ A ∧ lpReplicaCurrentReflect x ∈ C)) ∨ ((lpReplicaCurrentReflect x ∈ A ∧ lpReplicaCurrentReflect x ∈ C) ∧ ¬ (x ∈ A ∧ x ∉ C)) := by
-- proof
  apply StatMech.Ising.mem_lpReplicaPartialReflectSource A C x

/--
[lpReplicaOffdiagComponent_partialReflectSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaComponentReflection.lean)
-/
@[path]
private lemma lpReplicaOffdiagComponent_partialReflectSource_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let H := lpReplicaCurrentGraph G sites let K : Finset (Copy H m) := Finset.univ let e := endsM H m let C := RandomCurrent.compOf e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let A := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 lpReplicaPartialReflectSource A C = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∨ lpReplicaPartialReflectSource A C = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagComponent_partialReflectSource G sites hsite hij m hsrc hdisc

/--
[lpOffdiagPartialSource_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaComponentReflection.lean)
-/
@[path]
private lemma lpOffdiagPartialSource_complement_eq
  [Fintype V]
  [DecidableEq V]
  {Si Sj T P : Finset (LPReplicaCurrentVertex V)}
-- given
  (hP : P = Si ∨ P = Sj) :
-- imply
  (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨ (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpOffdiagPartialSource_complement Si Sj T P hP

/--
[lpReplicaOffdiagComponent_partialReflectAllocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaComponentReflection.lean)
-/
@[path]
private lemma lpReplicaOffdiagComponent_partialReflectAllocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsrc : RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1)
  (hdisc : ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ : Finset (Copy (lpReplicaCurrentGraph G sites) m)) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let H := lpReplicaCurrentGraph G sites let C := RandomCurrent.compOf (endsM H m) (Finset.univ : Finset (Copy H m)) (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 let P := lpReplicaPartialReflectSource (Si ∆ Sj ∆ T) C (P = Si ∧ (Si ∆ Sj ∆ T) ∆ P = Sj ∆ T) ∨ (P = Sj ∧ (Si ∆ Sj ∆ T) ∆ P = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagComponent_partialReflectAllocation G sites hsite hij m hsrc hdisc


-- created on 2026-10-23
