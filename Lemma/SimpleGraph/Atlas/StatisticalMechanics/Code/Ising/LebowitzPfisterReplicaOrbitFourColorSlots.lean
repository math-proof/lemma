import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
open Finset StatMech StatMech.Ising


/--
[colorClass_lpReplicaFourColorTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma colorClass_lpReplicaFourColorTransport_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {E : α ≃ β}
  {a : Fin 4}
-- given
  (color : ↑(Finset.univ : Finset α) -> Fin 4) :
-- imply
  colorClass Finset.univ (lpReplicaFourColorTransport E color) a = (colorClass Finset.univ color a).map E.toEmbedding := by
-- proof
  apply StatMech.Ising.colorClass_lpReplicaFourColorTransport E color a

/--
[rowClass_lpReplicaFourColorTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma rowClass_lpReplicaFourColorTransport_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  {E : α ≃ β}
  {r : Fin 2}
-- given
  (color : ↑(Finset.univ : Finset α) -> Fin 4) :
-- imply
  rowClass Finset.univ (lpReplicaFourColorTransport E color) r = (rowClass Finset.univ color r).map E.toEmbedding := by
-- proof
  apply StatMech.Ising.rowClass_lpReplicaFourColorTransport E color r

/--
[leftPattern_lpReplicaFourColorTransport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma leftPattern_lpReplicaFourColorTransport_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype α]
  [DecidableEq α]
  [Fintype β]
  [DecidableEq β]
  [Fintype W]
  [DecidableEq W]
  {E : α ≃ β}
  {A B : Finset W}
  {u v : W}
-- given
  (endsα : α -> Sym2 W)
  (endsβ : β -> Sym2 W)
  (hends : forall x, endsβ (E x) = endsα x)
  (color : ↑(Finset.univ : Finset α) -> Fin 4)
  (hleft : LeftPattern endsα Finset.univ A B u v color) :
-- imply
  LeftPattern endsβ Finset.univ A B u v (lpReplicaFourColorTransport E color) := by
-- proof
  apply StatMech.Ising.leftPattern_lpReplicaFourColorTransport E endsα endsβ hends A B u v color hleft

/--
[lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V)
  (hfixed : e ∉ lpReplicaCurrentEdgeOrbitFixed G sites)
  (hstrict : e ∉ lpReplicaCurrentEdgeOrbitStrictReps G sites) :
-- imply
  lpReplicaCurrentEdgeReflect G sites e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_reflect_mem_strictReps_of_not_mem G sites e hfixed hstrict

/--
[lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm (Sum.inl e) = e.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed G sites e

/--
[lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm (Sum.inr (Sum.inl e)) = e.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict G sites e

/--
[lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm (Sum.inr (Sum.inr e)) = lpReplicaCurrentEdgeReflect G sites e.1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict G sites e

/--
[lpReplicaProfile_eq_half_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfile_eq_half_of_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  m e.1 = q e.1 / 2 := by
-- proof
  apply StatMech.Ising.lpReplicaProfile_eq_half_of_fixed G sites q m hm e

/--
[lpReplicaProfile_eq_of_orbitLabel_allocation_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfile_eq_of_orbitLabel_allocation_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {M : LPReplicaProfileOrbitLabel G sites q n}
-- given
  (sites : I -> V)
  (q m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (hn : lpReplicaSymmetrizedProfile G sites n = q)
  (halloc : (fun e => (L e).1) = fun e => (M e).1) :
-- imply
  m = n := by
-- proof
  apply StatMech.Ising.lpReplicaProfile_eq_of_orbitLabel_allocation_eq G sites q m n hm hn L M halloc

/--
[lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (m e.1)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e (Sum.inl k) ∈ (L e).1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitPairedCoordEquivSlot_apply_left_mem G sites q m hm L e k

/--
[lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e (Sum.inr k) ∉ (L e).1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitPairedCoordEquivSlot_apply_right_not_mem G sites q m hm L e k

/--
[lpReplicaProfileCopyEquivOrbitCoord_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivOrbitCoord_fst_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaProfileCopyEquivOrbitCoord G sites m c).1 = lpReplicaCurrentEdgeOrbitCoordEquiv G sites c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivOrbitCoord_fst G sites m c

/--
[lpReplicaProfileCopyEquivOrbitCoord_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivOrbitCoord_snd_val_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaProfileCopyEquivOrbitCoord G sites m c).2.1 = c.2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivOrbitCoord_snd_val G sites m c

/--
[lpReplicaProfileCopyEquivOrbitCoord_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivOrbitCoord_edge_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm (lpReplicaProfileCopyEquivOrbitCoord G sites m c).1 = c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivOrbitCoord_edge G sites m c

/--
[card_lpReplicaOrbitCommonSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma card_lpReplicaOrbitCommonSlot_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Fintype.card (LPReplicaOrbitCommonSlot G sites q) = (∑ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites), q e.1 / 2) + ∑ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), q e.1 := by
-- proof
  apply StatMech.Ising.card_lpReplicaOrbitCommonSlot G sites q

/--
[lpReplicaOrbitProfileCoordEquivCommonSlot_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitProfileCoordEquivCommonSlot_fixed_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)}
  {k : Fin (m e.1)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L ⟨Sum.inl e, k⟩ = Sum.inl ⟨e, Equiv.cast (congrArg Fin (lpReplicaProfile_eq_half_of_fixed G sites q m hm e)) k⟩ := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitProfileCoordEquivCommonSlot_fixed G sites q m hm L e k

/--
[lpReplicaOrbitProfileCoordEquivCommonSlot_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitProfileCoordEquivCommonSlot_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (m e.1)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L ⟨Sum.inr (Sum.inl e), k⟩ = Sum.inr ⟨e, lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e (Sum.inl k)⟩ := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitProfileCoordEquivCommonSlot_strict G sites q m hm L e k

/--
[lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L ⟨Sum.inr (Sum.inr e), k⟩ = Sum.inr ⟨e, lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e (Sum.inr k)⟩ := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitProfileCoordEquivCommonSlot_reflectStrict G sites q m hm L e k

/--
[lpReplicaProfileCopyEquivCommonSlot_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivCommonSlot_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (m e.1)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaProfileCopyEquivCommonSlot G sites q m hm L ⟨e.1, k⟩ = Sum.inr ⟨e, lpReplicaProfileOrbitLabelRepEmbedding G sites q m L e k⟩ := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivCommonSlot_strict G sites q m hm L e k

/--
[lpReplicaProfileCopyEquivCommonSlot_reflectStrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileCopyEquivCommonSlot_reflectStrict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (m (lpReplicaCurrentEdgeReflect G sites e.1))}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaProfileCopyEquivCommonSlot G sites q m hm L ⟨lpReplicaCurrentEdgeReflect G sites e.1, k⟩ = Sum.inr ⟨e, lpReplicaProfileOrbitLabelReflectEmbedding G sites q m hm L e k⟩ := by
-- proof
  apply StatMech.Ising.lpReplicaProfileCopyEquivCommonSlot_reflectStrict G sites q m hm L e k

/--
[lpReplicaOrbitFourColorSlotStateOfTag_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotStateOfTag_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).allocation = fun e => (L e).1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotStateOfTag_allocation G sites q m hm L tag

/--
[lpReplicaOrbitFourColorSlotStateOfTag_color_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotStateOfTag_color_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag).color ⟨lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c, Finset.mem_univ _⟩ = lpReplicaRowTagEquivFin4 (tag c) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotStateOfTag_color_copy G sites q m hm L tag c

/--
[LPReplicaOrbitFourColorSlotState.ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma ext_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {s t : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (ha : s.allocation = t.allocation)
  (hc : s.color = t.color) :
-- imply
  s = t := by
-- proof
  apply StatMech.Ising.LPReplicaOrbitFourColorSlotState.ext ha hc

/--
[lpReplicaOrbitFourColorSlotStateOfTag_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotStateOfTag_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  Function.Injective (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotStateOfTag_injective G sites q m hm L

/--
[lpReplicaRowToggleFin4_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaRowToggleFin4_involutive_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Function.Involutive lpReplicaRowToggleFin4 := by
-- proof
  apply StatMech.Ising.lpReplicaRowToggleFin4_involutive

/--
[lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst_eq
  [Fintype V]
  [DecidableEq V]
  {a : Fin 4} :
-- imply
  (lpReplicaRowTagEquivFin4.symm (lpReplicaRowToggleFin4 a)).1 = !(lpReplicaRowTagEquivFin4.symm a).1 := by
-- proof
  apply StatMech.Ising.lpReplicaRowTagEquivFin4_symm_rowToggleFin4_fst a

/--
[lpReplicaOrbitFourColorSlotRowToggle_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRowToggle_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotRowToggle G sites q P) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRowToggle_involutive G sites q P

/--
[mem_lpReplicaOrbitCommonSlotsOfCopies_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma mem_lpReplicaOrbitCommonSlotsOfCopies_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {x : LPReplicaOrbitCommonSlot G sites q}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  x ∈ lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P ↔ (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L).symm x ∈ P := by
-- proof
  apply StatMech.Ising.mem_lpReplicaOrbitCommonSlotsOfCopies_iff G sites q m hm L P x

/--
[lpReplicaOrbitFourColorSlotRowToggle_stateOfTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRowToggle_stateOfTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaOrbitFourColorSlotRowToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) = lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L (lpReplicaToggleRows G sites m P tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRowToggle_stateOfTag G sites q m hm L P tag

/--
[lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) = c.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy G sites q m hm L tag c

/--
[lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {c : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  lpReplicaOrbitFourColorSlotEnds G sites q (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) (lpReplicaProfileCopyEquivCommonSlot G sites q m hm L c) = StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m c := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEnds_stateOfTag_copy G sites q m hm L tag c

/--
[lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitFourColorSelectedStrictSlots G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) e = ((lpReplicaProfileOrbitSelectedLabelOfCopies G sites q m hm P L).2 e).1.1 ∪ ((lpReplicaProfileOrbitSelectedLabelOfCopies G sites q m hm P L).2 e).2.1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies G sites q m hm L P e

/--
[lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaOrbitFourColorSlotReflectFamily G sites q (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation = (lpReplicaProfileOrbitSlotMove G sites q (lpReplicaProfileOrbitSelectedLabelEquivSlotFiber G sites q m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P) (lpReplicaProfileOrbitSelectedLabelOfCopies G sites q m hm P L)).1).allocation := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectFamily_ofCopies_allocation G sites q m hm L P tag

/--
[lpReplicaProfileOrbitLabelPartialReflectCopies_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L) e).1) = (lpReplicaOrbitFourColorSlotReflectFamily G sites q (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitLabelPartialReflectCopies_allocation G sites q m hm L P tag

/--
[lpReplicaOrbitFourColorSlotReflectFamily_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflectFamily_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Finset (Fin (q e.1))}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotReflectFamily G sites q P) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflectFamily_involutive G sites q P

/--
[lpReplicaOrbitFourColorSlotReflect_eq_reflectFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflect_eq_reflectFamily_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotReflect G sites q P s = lpReplicaOrbitFourColorSlotReflectFamily G sites q (lpReplicaOrbitFourColorSelectedStrictSlots G sites q P) s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflect_eq_reflectFamily G sites q P s

/--
[lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q) :
-- imply
  lpReplicaOrbitFourColorSlotReflect G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) s = lpReplicaOrbitFourColorSlotReflectFamily G sites q (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P) s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflect_commonSlotsOfCopies G sites q m hm L P s

/--
[lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L) e).1) = (lpReplicaOrbitFourColorSlotReflect G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitLabelPartialReflectCopies_allocation_commonSlots G sites q m hm L P tag

/--
[lpReplicaOrbitFourColorSlotRecolor_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRecolor_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {X Y : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOrbitFourColorSlotRecolor G sites q X Y s).allocation = s.allocation := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRecolor_allocation G sites q X Y s

/--
[lpReplicaOrbitFourColorSlotRecolor_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRecolor_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {X Y : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotRecolor G sites q X Y) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRecolor_involutive G sites q X Y

/--
[lpReplicaOrbitFourColorSlotReflect_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotReflect_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotReflect G sites q P) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotReflect_involutive G sites q P

/--
[lpReplicaOrbitFourColorSlotCrossRecolor_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossRecolor_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P X Y : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotCrossRecolor G sites q P X Y) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossRecolor_involutive G sites q P X Y

/--
[lpReplicaOrbitFourColorSlotCrossToggle_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaOrbitFourColorSlotCrossToggle G sites q P) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_involutive G sites q P

/--
[lpReplicaOrbitFourColorSlotCrossToggle_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_comp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P Q : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotCrossToggle G sites q P (lpReplicaOrbitFourColorSlotCrossToggle G sites q Q s) = lpReplicaOrbitFourColorSlotCrossToggle G sites q (P ∆ Q) s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_comp G sites q P Q s

/--
[lpReplicaOrbitFourColorSlotRowMask_crossToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotRowMask_crossToggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotRowMask G sites q (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) = lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ P := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotRowMask_crossToggle G sites q P s

/--
[lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotCrossNormalize G sites q (lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) = lpReplicaOrbitFourColorSlotCrossNormalize G sites q s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossNormalize_crossToggle G sites q P s

/--
[lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitFourColorSlotRowMask G sites q s) (lpReplicaOrbitFourColorSlotCrossNormalize G sites q s) = s := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_rowMask_crossNormalize G sites q s

/--
[lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s t : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  s = t ↔ lpReplicaOrbitFourColorSlotCrossNormalize G sites q s = lpReplicaOrbitFourColorSlotCrossNormalize G sites q t ∧ lpReplicaOrbitFourColorSlotRowMask G sites q s = lpReplicaOrbitFourColorSlotRowMask G sites q t := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq G sites q s t

/--
[lpReplicaOrbitFourColorSlotCrossToggle_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_eq_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P Q : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s t : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotCrossToggle G sites q P s = lpReplicaOrbitFourColorSlotCrossToggle G sites q Q t ↔ lpReplicaOrbitFourColorSlotCrossNormalize G sites q s = lpReplicaOrbitFourColorSlotCrossNormalize G sites q t ∧ lpReplicaOrbitFourColorSlotRowMask G sites q s ∆ P = lpReplicaOrbitFourColorSlotRowMask G sites q t ∆ Q := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_eq_iff G sites q P Q s t

/--
[exists_crossToggle_eq_iff_crossNormalize_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma exists_crossToggle_eq_iff_crossNormalize_eq_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s t : LPReplicaOrbitFourColorSlotState G sites q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (∃ P : Finset (LPReplicaOrbitCommonSlot G sites q), t = lpReplicaOrbitFourColorSlotCrossToggle G sites q P s) ↔ lpReplicaOrbitFourColorSlotCrossNormalize G sites q t = lpReplicaOrbitFourColorSlotCrossNormalize G sites q s := by
-- proof
  apply StatMech.Ising.exists_crossToggle_eq_iff_crossNormalize_eq G sites q s t

/--
[lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (encode : α -> LPReplicaOrbitFourColorSlotState G sites q)
  (selector : α -> Finset (LPReplicaOrbitCommonSlot G sites q))
  (branch : α -> β)
  (hencode : Function.Injective encode)
  (hstable : forall a b, (branch a, lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector a) (encode a)) = (branch b, lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector b) (encode b)) -> selector a = selector b) :
-- imply
  Function.Injective fun a => (branch a, lpReplicaOrbitFourColorSlotCrossToggle G sites q (selector a) (encode a)) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotBranchedCrossToggle_injective_of_collisionStable G sites q encode selector branch hencode hstable

/--
[lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation = fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L) e).1 := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation G sites q m hm L P tag

/--
[lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag) :
-- imply
  (lpReplicaOrbitFourColorSlotCrossToggle G sites q (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).color = (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L (lpReplicaToggleRows G sites m P tag)).color := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color G sites q m hm L P tag

/--
[lpReplicaOrbitFourColorSlotEdge_reflect_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotEdge_reflect_strict_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {P : Finset (LPReplicaOrbitCommonSlot G sites q)}
  {s : LPReplicaOrbitFourColorSlotState G sites q}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
  {k : Fin (q e.1)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOrbitFourColorSlotEdge G sites q (lpReplicaOrbitFourColorSlotReflect G sites q P s) (Sum.inr ⟨e, k⟩) = if (Sum.inr ⟨e, k⟩ : LPReplicaOrbitCommonSlot G sites q) ∈ P then lpReplicaCurrentEdgeReflect G sites (lpReplicaOrbitFourColorSlotEdge G sites q s (Sum.inr ⟨e, k⟩)) else lpReplicaOrbitFourColorSlotEdge G sites q s (Sum.inr ⟨e, k⟩) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotEdge_reflect_strict G sites q P s e k

/--
[lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {u v : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (hleft : LeftPattern (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m) Finset.univ A B u v (lpReplicaTagFourColor G sites m tag)) :
-- imply
  LPReplicaOrbitFourColorSlotLeftPattern G sites q A B u v (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag) := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotLeftPattern_stateOfTag G sites q m hm L tag A B u v hleft

/--
[lpReplicaOrbitFourColorSlotLeftPattern_partialReflectCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrbitFourColorSlotLeftPattern_partialReflectCopies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {L : LPReplicaProfileOrbitLabel G sites q m}
  {P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {u v : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hm : lpReplicaSymmetrizedProfile G sites m = q)
  (tag : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag)
  (tag' : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) (lpReplicaPartialReflectProfile G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P)) -> LPReplicaRowTag)
  (hleft : LeftPattern (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) (lpReplicaPartialReflectProfile G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P))) Finset.univ A B u v (lpReplicaTagFourColor G sites (lpReplicaPartialReflectProfile G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P)) tag')) :
-- imply
  let m' := lpReplicaPartialReflectProfile G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P) let hm' : lpReplicaSymmetrizedProfile G sites m' = q := (lpReplicaSymmetrizedProfile_partialReflect G sites m (StatMech.Sharpness.FluxEdgeCopy.profileFlux (lpReplicaCurrentGraph G sites) m P) (StatMech.Sharpness.FluxEdgeCopy.profileFlux_le (lpReplicaCurrentGraph G sites) m P)).trans hm let L' := lpReplicaProfileOrbitLabelPartialReflectCopies G sites q m hm P L let s' := lpReplicaOrbitFourColorSlotStateOfTag G sites q m' hm' L' tag' s'.allocation = (lpReplicaOrbitFourColorSlotReflectFamily G sites q (lpReplicaOrbitSpatialSelectorOfCopies G sites q m hm L P) (lpReplicaOrbitFourColorSlotStateOfTag G sites q m hm L tag)).allocation ∧ LPReplicaOrbitFourColorSlotLeftPattern G sites q A B u v s' := by
-- proof
  apply StatMech.Ising.lpReplicaOrbitFourColorSlotLeftPattern_partialReflectCopies G sites q m hm L P tag tag' A B u v hleft

/--
[lpReplicaOrientedFourColorSlotState_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorSlotState_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Injective (lpReplicaOrientedFourColorSlotState G sites A B q) := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorSlotState_injective G sites A B q

/--
[lpReplicaOrientedFourColorSlotState_leftPattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean)
-/
@[path]
private lemma lpReplicaOrientedFourColorSlotState_leftPattern_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A B : Finset (LPReplicaCurrentVertex V)}
  {z : LPReplicaOrientedFourColorAtom G sites A B q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOrbitFourColorSlotLeftPattern G sites q A (B.map lpReplicaCurrentReflect.toEmbedding) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 (lpReplicaOrientedFourColorSlotState G sites A B q z) := by
-- proof
  apply StatMech.Ising.lpReplicaOrientedFourColorSlotState_leftPattern G sites A B q z


-- created on 2026-10-23
