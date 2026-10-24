import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove
open Finset StatMech StatMech.Ising


/--
[LPReplicaPooledSelectedSlotState.ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma ext_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {x y : LPReplicaPooledSelectedSlotState G sites q}
-- given
  (hprofile : x.profile = y.profile)
  (hselected : x.selected = y.selected)
  (hslots : x.slots = y.slots) :
-- imply
  x = y := by
-- proof
  apply StatMech.Ising.LPReplicaPooledSelectedSlotState.ext hprofile hselected hslots

/--
[lpReplicaPooledSelectedSlotMove_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotMove_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaPooledSelectedSlotMove G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotMove_involutive G sites q

/--
[lpReplicaPooledSelectedSlotStateOfCopies_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotStateOfCopies_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  (lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L).profile = m := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotStateOfCopies_profile G sites m q hm P L

/--
[lpReplicaPooledSelectedSlotStateOfCopies_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotStateOfCopies_selected_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  (lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L).selected = StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotStateOfCopies_selected G sites m q hm P L

/--
[lpReplicaPooledSelectedSlotMove_ofCopies_profile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotMove_ofCopies_profile_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  (lpReplicaPooledSelectedSlotMove G sites q (lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L)).profile = lpReplicaPartialReflectProfile G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P) := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotMove_ofCopies_profile G sites m q hm P L

/--
[lpReplicaPooledSelectedSlotMove_ofCopies_orbitLabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotMove_ofCopies_orbitLabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  ((lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm (lpReplicaPooledSelectedSlotMove G sites q (lpReplicaPooledSelectedSlotStateOfCopies G sites m q hm P L))).2.2.1 = lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotMove_ofCopies_orbitLabel G sites m q hm P L

/--
[lpReplicaPooledSelectedSlotMove_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotMove_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaPooledSelectedSlotMove G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotMove_injective G sites q

/--
[card_image_lpReplicaPooledSelectedSlotMove](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma card_image_lpReplicaPooledSelectedSlotMove_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (LPReplicaPooledSelectedSlotState G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (S.image (lpReplicaPooledSelectedSlotMove G sites q)).card = S.card := by
-- proof
  apply StatMech.Ising.card_image_lpReplicaPooledSelectedSlotMove G sites q S

/--
[lpReplicaPooledSelectedSlotMove_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean)
-/
@[path]
private lemma lpReplicaPooledSelectedSlotMove_hall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset (LPReplicaPooledSelectedSlotState G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  S.card <= (S.biUnion fun z => {lpReplicaPooledSelectedSlotMove G sites q z}).card := by
-- proof
  apply StatMech.Ising.lpReplicaPooledSelectedSlotMove_hall G sites q S


-- created on 2026-10-23
