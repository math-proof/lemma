import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFourFunctions
open Finset StatMech StatMech.Ising


/--
[lpReplicaMatchingDisconn_le_of_offdiagFourFunctions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFourFunctions.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_offdiagFourFunctions_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hpoint : ∀ i j : I, i ≠ j -> let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr (Si ∆ Sj ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= sourcePairDisconnSum H beta Jr Si ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr (Sj ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 + sourcePairDisconnSum H beta Jr Sj ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr (Si ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_offdiagFourFunctions G sites beta J hf r hbeta hJ hhf hr hpoint


-- created on 2026-10-23
