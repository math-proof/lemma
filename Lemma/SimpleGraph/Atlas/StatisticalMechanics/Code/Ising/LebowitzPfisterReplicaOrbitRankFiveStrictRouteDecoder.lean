import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part3
open StatMech StatMech.Ising


/--
[lpReplicaOrbitFourColorSlotReflectRowToggle_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectRowToggle_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {spatial row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row s).allocation = (lpReplicaOrbitFourColorSlotReflect G sites q spatial s).allocation := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectRowToggle_allocation G sites q spatial row s

/--
[lpReplicaOrbitFourColorSlotReflectRowToggle_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectRowToggle_color_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {spatial row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {x : ↑(Finset.univ : Finset (LPReplicaOrbitCommonSlot G sites q))}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row s).color x = if x.1 ∈ row then lpReplicaRowToggleFin4 (s.color x) else s.color x := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectRowToggle_color G sites q spatial row s x

/--
[lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {spatial row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row s) = lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ row := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRowMask_reflectRowToggle G sites q spatial row s

/--
[lpReplicaOrbitFourColorSlotStateOfTag_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotStateOfTag_color_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {x : ↑(Finset.univ : Finset (LPReplicaOrbitCommonSlot G sites q))}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).color x = lpReplicaRowTagEquivFin4 (tag ((lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).symm x.1)) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotStateOfTag_color G sites q m hm L tag x

/--
[lpReplicaSingletonFalseRowTag_equivFin4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaSingletonFalseRowTag_equivFin4_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq C]
  {c a : C} :
-- imply
  lpReplicaRowTagEquivFin4 (lpReplicaSingletonFalseRowTag c a) = if a = c then lpReplicaRowToggleFin4 (lpReplicaRowTagEquivFin4 (true, false)) else lpReplicaRowTagEquivFin4 (true, false) := by
-- proof
  apply StatMech.Ising.lpReplicaSingletonFalseRowTag_equivFin4 c a

/--
[lpReplicaOrbitFourColorSlotReflectRowToggle_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectRowToggle_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {spatial row : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectRowToggle_involutive G sites q spatial row

/--
[lpReplicaOrbitFourColorSlotReflectRowToggle_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectRowToggle_comm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {spatial₀ spatial₁ row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row s) = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row s) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectRowToggle_comm G sites q spatial₀ spatial₁ row s

/--
[lpReplicaOrbitFourColorSlotReflectRowToggle_crossed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectRowToggle_crossed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {spatial₀ spatial₁ row : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s t : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcross : lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row s = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row t) :
-- imply
  lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₁ row s = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial₀ row t := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectRowToggle_crossed G sites q spatial₀ spatial₁ row s t hcross

/--
[lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (rawTag : Copy (lpReplicaCurrentGraph G sites) (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) -> LPReplicaRowTag)
  (hraw : LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) m (Finset.univ \ P)) (profileFlux (lpReplicaCurrentGraph G sites) m P)) A B rawTag) :
-- imply
  let target := lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m P) let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv G sites q m hm L P let tag := lpReplicaTransportTag G sites relabel rawTag let atom := lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect G sites q m hm L P rawTag A B hraw lpReplicaOrientedFourColorSlotState G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q atom) = lpReplicaOrbitFourColorSlotStateOfTag G sites q target ((lpReplicaSymmetrizedProfile_partialReflectCopies G sites m P).trans hm) (lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L) tag := by
-- proof
  apply StatMech.Ising.lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect_slotState G sites q m hm L P rawTag A B hraw

/--
[lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z = lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1 z.1.1.2 z.2.2 (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceSlotState_eq_rowGateData G sites i j q z

/--
[lpReplicaStrictRouteSingletonTag_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaStrictRouteSingletonTag_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c d : Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (sourceTag : Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hsource : ∀ e, sourceTag e = (true, false)) :
-- imply
  let rawCopy := lpReplicaPartialReflectCopyEquivRaw G sites m {d} let rawTag := lpReplicaSingletonFalseRowTag (rawCopy c) let target := lpReplicaPartialReflectProfile G sites m (profileFlux (lpReplicaCurrentGraph G sites) m {d}) let relabel := lpReplicaPartialReflectCanonicalRelabelEquiv G sites q m hm L {d} let targetTag := lpReplicaTransportTag G sites relabel rawTag let spatial := lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {d} let row := lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L {c} lpReplicaOrbitFourColorSlotStateOfTag G sites q target ((lpReplicaSymmetrizedProfile_partialReflectCopies G sites m {d}).trans hm) (lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm {d} L) targetTag = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatial row (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L sourceTag) := by
-- proof
  apply StatMech.Ising.lpReplicaStrictRouteSingletonTag_slotState G sites q m hm L c d sourceTag hsource

/--
[lpReplicaOffdiagDecoratedSourceCanonicalSingletonStrictRoute_slotState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSourceCanonicalSingletonStrictRoute_slotState_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
  {c d : Copy (lpReplicaCurrentGraph G sites) z.1.1.1}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hraw : LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 (Finset.univ \ {d})) (profileFlux (lpReplicaCurrentGraph G sites) z.1.1.1 {d})) A B (lpReplicaSingletonFalseRowTag (lpReplicaPartialReflectCopyEquivRaw G sites z.1.1.1 {d} c)))
  (hsource : ∀ e, (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 e = (true, false)) :
-- imply
  let atom := lpReplicaDecoratedOrbitAtomCanonicalizeRawPartialReflect G sites q z.1.1.1 z.1.1.2 z.2.2 {d} (lpReplicaSingletonFalseRowTag (lpReplicaPartialReflectCopyEquivRaw G sites z.1.1.1 {d} c)) A B hraw lpReplicaOrientedFourColorSlotState G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites A (B.map lpReplicaCurrentReflect.toEmbedding) q atom) = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {d}) (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2 {c}) (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSourceCanonicalSingletonStrictRoute_slotState G sites i j q z c d A B hraw hsource

/--
[lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z w : LPReplicaOffdiagDecoratedSource G sites i j q}
  {spatialZ rowZ spatialW rowW : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {targetZ targetW : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hz : targetZ = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatialZ rowZ (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))
  (hw : targetW = lpReplicaOrbitFourColorSlotReflectRowToggle G sites q spatialW rowW (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w))
  (hspatial : spatialZ = spatialW)
  (hrow : rowZ = rowW)
  (htarget : targetZ = targetW) :
-- imply
  z = w := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision G sites i j q z w spatialZ rowZ spatialW rowW targetZ targetW hz hw hspatial hrow htarget

/--
[card_lpReplicaStrictRouteMaskKey_rankFive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma card_lpReplicaStrictRouteMaskKey_rankFive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card (LPReplicaStrictRouteMaskKey G sites q) = 20 := by
-- proof
  apply StatMech.Ising.card_lpReplicaStrictRouteMaskKey_rankFive G sites q hcard

/--
[LPReplicaStrictRouteStateFamily.target_fiber_card_le_twenty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma target_fiber_card_le_twenty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {i j : I}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  [Fintype Source]
  [DecidableEq Target]
  {F : LPReplicaStrictRouteStateFamily G sites i j q Source Target}
  {t : Target}
-- given
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card {x : Source // F.target x = t} ≤ 20 := by
-- proof
  apply StatMech.Ising.LPReplicaStrictRouteStateFamily.target_fiber_card_le_twenty F hcard t

/--
[LPReplicaStrictRouteStateFamily.rowSlot_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma rowSlot_eq_of_target_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {i j : I}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {F : LPReplicaStrictRouteStateFamily G sites i j q Source Target}
  {x y : Source}
-- given
  (hsourceRow : ∀ x, lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q (F.source x)) = Finset.univ)
  (htarget : F.target x = F.target y) :
-- imply
  F.rowSlot x = F.rowSlot y := by
-- proof
  apply StatMech.Ising.LPReplicaStrictRouteStateFamily.rowSlot_eq_of_target_eq F hsourceRow htarget

/--
[LPReplicaStrictRouteStateFamily.eq_of_spatialSlot_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma eq_of_spatialSlot_eq_of_target_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {i j : I}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {F : LPReplicaStrictRouteStateFamily G sites i j q Source Target}
  {x y : Source}
-- given
  (hsourceRow : ∀ x, lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q (F.source x)) = Finset.univ)
  (hspatial : F.spatialSlot x = F.spatialSlot y)
  (htarget : F.target x = F.target y) :
-- imply
  x = y := by
-- proof
  apply StatMech.Ising.LPReplicaStrictRouteStateFamily.eq_of_spatialSlot_eq_of_target_eq F hsourceRow hspatial htarget

/--
[LPReplicaStrictRouteStateFamily.saturated_target_fiber_card_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma saturated_target_fiber_card_le_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {i j : I}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  [Fintype Source]
  [DecidableEq Target]
  {F : LPReplicaStrictRouteStateFamily G sites i j q Source Target}
  {t : Target}
-- given
  (hsourceRow : ∀ x, lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q (F.source x)) = Finset.univ)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card {x : Source // F.target x = t} ≤ 4 := by
-- proof
  apply StatMech.Ising.LPReplicaStrictRouteStateFamily.saturated_target_fiber_card_le_four F hsourceRow hcard t

/--
[LPReplicaStrictRouteStateFamily.card_le_twenty_mul_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean)
-/
@[path]
private lemma card_le_twenty_mul_target_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {i j : I}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  [Fintype Source]
  [Fintype Target]
  {F : LPReplicaStrictRouteStateFamily G sites i j q Source Target}
-- given
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  Fintype.card Source ≤ 20 * Fintype.card Target := by
-- proof
  apply StatMech.Ising.LPReplicaStrictRouteStateFamily.card_le_twenty_mul_target F hcard


-- created on 2026-10-23
