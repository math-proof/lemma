import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaGhostComponent
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagSource_eq_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaGhostComponent.lean)
-/
@[path]
private lemma lpReplicaOffdiagSource_eq_six_eq
  [Fintype V]
  [DecidableEq V]
  {i j : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j) :
-- imply
  lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 = {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i, lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagSource_eq_six sites hsite hij

/--
[lpReplicaGhostComponent_splits_exactly_one_markedSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaGhostComponent.lean)
-/
@[path]
private lemma lpReplicaGhostComponent_splits_exactly_one_markedSeam_eq
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
  let ciL := RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ lpReplicaCurrentGhost0 (lpReplicaCurrentLeft sites i) let ciR := RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ lpReplicaCurrentGhost0 (lpReplicaCurrentRight sites i) let cjL := RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ lpReplicaCurrentGhost0 (lpReplicaCurrentLeft sites j) let cjR := RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ lpReplicaCurrentGhost0 (lpReplicaCurrentRight sites j) let splitI := (ciL ∧ ¬ ciR) ∨ (¬ ciL ∧ ciR) let splitJ := (cjL ∧ ¬ cjR) ∨ (¬ cjL ∧ cjR) (splitI ∧ ¬ splitJ) ∨ (¬ splitI ∧ splitJ) := by
-- proof
  apply StatMech.Ising.lpReplicaGhostComponent_splits_exactly_one_markedSeam G sites hsite hij m hsrc hdisc


-- created on 2026-10-23
