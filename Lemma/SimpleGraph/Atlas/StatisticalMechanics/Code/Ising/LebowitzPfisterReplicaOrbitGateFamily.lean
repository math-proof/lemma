import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitGateFamily
open Finset StatMech StatMech.Ising


/--
[lpReplicaDisconnFamilies_partialReflect_offdiag_swapRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitGateFamily.lean)
-/
@[path]
private lemma lpReplicaDisconnFamilies_partialReflect_offdiag_swapRows_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites ∅ a)
  (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites (lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆ lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1) b) :
-- imply
  let m := lpReplicaCollisionProfile G sites a b let tag := lpReplicaCollisionRowTag G sites a b Sa Sb let e := endsM (lpReplicaCurrentGraph G sites) m let K := lpReplicaRowCopies G sites m tag true let P := edgeComponent e K (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) let target := lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P) let movedTag := lpReplicaSwapRowsTag (lpReplicaPartialReflectTagRaw G sites m P tag) let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 (LPReplicaRowGate G sites target Si ∅ movedTag ∧ (Si ∆ Sj ∆ T) ∆ Si = Sj ∆ T) ∨ (LPReplicaRowGate G sites target Sj ∅ movedTag ∧ (Si ∆ Sj ∆ T) ∆ Sj = Si ∆ T) := by
-- proof
  apply StatMech.Ising.lpReplicaDisconnFamilies_partialReflect_offdiag_swapRows G sites hsite hij a b Sa Sb hSa hSb


-- created on 2026-10-23
