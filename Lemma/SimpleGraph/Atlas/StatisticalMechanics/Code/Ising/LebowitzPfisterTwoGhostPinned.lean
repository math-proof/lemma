import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostPinned.Part5
open Finset StatMech StatMech.Ising


/--
[lpTwoGhostPinnedConfig_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostPinnedConfig_inl_eq
  [Fintype W]
  [DecidableEq W]
  {tau : ConfigSpace W}
  {x : W} :
-- imply
  lpTwoGhostPinnedConfig tau (.inl x) = tau x := by
-- proof
  apply StatMech.Ising.lpTwoGhostPinnedConfig_inl tau x

/--
[lpTwoGhostPinnedConfig_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostPinnedConfig_inr_eq
  [Fintype W]
  [DecidableEq W]
  {tau : ConfigSpace W}
  {b : Bool} :
-- imply
  lpTwoGhostPinnedConfig tau (.inr b) = !b := by
-- proof
  apply StatMech.Ising.lpTwoGhostPinnedConfig_inr tau b

/--
[spin_lpTwoGhostPinnedConfig_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma spin_lpTwoGhostPinnedConfig_inl_eq
  [Fintype W]
  [DecidableEq W]
  {tau : ConfigSpace W}
  {x : W} :
-- imply
  spin (lpTwoGhostPinnedConfig tau) (.inl x) = spin tau x := by
-- proof
  apply StatMech.Ising.spin_lpTwoGhostPinnedConfig_inl tau x

/--
[spin_lpTwoGhostPinnedConfig_inr_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma spin_lpTwoGhostPinnedConfig_inr_false_eq
  [Fintype W]
  [DecidableEq W]
  {tau : ConfigSpace W} :
-- imply
  spin (lpTwoGhostPinnedConfig tau) (.inr false) = 1 := by
-- proof
  apply StatMech.Ising.spin_lpTwoGhostPinnedConfig_inr_false tau

/--
[spin_lpTwoGhostPinnedConfig_inr_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma spin_lpTwoGhostPinnedConfig_inr_true_eq
  [Fintype W]
  [DecidableEq W]
  {tau : ConfigSpace W} :
-- imply
  spin (lpTwoGhostPinnedConfig tau) (.inr true) = -1 := by
-- proof
  apply StatMech.Ising.spin_lpTwoGhostPinnedConfig_inr_true tau

/--
[lpTwoGhostStarEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostStarEdge_injective_eq
  [Fintype W]
  [DecidableEq W]
-- given
  (side : W -> Bool) :
-- imply
  Function.Injective ((fun x : W => s(Sum.inl x, Sum.inr (side x))) : W -> Sym2 (LPTwoGhostVertex W)) := by
-- proof
  apply StatMech.Ising.lpTwoGhostStarEdge_injective side

/--
[lpTwoGhostBaseEdges_disjoint_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostBaseEdges_disjoint_star_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
-- given
  (side : W -> Bool) :
-- imply
  Disjoint (lpTwoGhostBaseEdges E) (lpTwoGhostStarEdges side) := by
-- proof
  apply StatMech.Ising.lpTwoGhostBaseEdges_disjoint_star E side

/--
[lpTwoGhostCoupling_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostCoupling_base_eq
  [Fintype W]
  [DecidableEq W]
  {x y : W}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool) :
-- imply
  lpTwoGhostCoupling J h side s(Sum.inl x, Sum.inl y) = J s(x, y) := by
-- proof
  apply StatMech.Ising.lpTwoGhostCoupling_base J h side x y

/--
[lpTwoGhostCoupling_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostCoupling_star_eq
  [Fintype W]
  [DecidableEq W]
  {x : W}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool) :
-- imply
  lpTwoGhostCoupling J h side s(Sum.inl x, Sum.inr (side x)) = h x := by
-- proof
  apply StatMech.Ising.lpTwoGhostCoupling_star J h side x

/--
[lpTwoGhostCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhostCoupling_nonneg_eq
  [Fintype W]
  [DecidableEq W]
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool)
  (hJ : forall e, 0 <= J e)
  (hh : forall x, 0 <= h x) :
-- imply
  forall e, 0 <= lpTwoGhostCoupling J h side e := by
-- proof
  apply StatMech.Ising.lpTwoGhostCoupling_nonneg J h side hJ hh

/--
[lpTwoGhost_bondSum_pinned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_bondSum_pinned_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {tau : ConfigSpace W}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool) :
-- imply
  (∑ e ∈ lpTwoGhostEdges E side, lpTwoGhostCoupling J h side e * bond (lpTwoGhostPinnedConfig tau) e) = (∑ e ∈ E, J e * bond tau e) + ∑ x : W, lpTwoGhostMixedField h side x * spin tau x := by
-- proof
  apply StatMech.Ising.lpTwoGhost_bondSum_pinned E J h side tau

/--
[lpTwoGhost_weight_pinned_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_weight_pinned_eq_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
  {tau : ConfigSpace W}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool) :
-- imply
  wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side) (fun _ => 0) (lpTwoGhostPinnedConfig tau) = wJ E J (lpTwoGhostMixedField h side) tau := by
-- proof
  apply StatMech.Ising.lpTwoGhost_weight_pinned_eq E J h side tau

/--
[lpTwoGhost_pinnedPartition_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_pinnedPartition_eq_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool) :
-- imply
  (∑ tau : ConfigSpace W, wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side) (fun _ => 0) (lpTwoGhostPinnedConfig tau)) = ZJ E J (lpTwoGhostMixedField h side) := by
-- proof
  apply StatMech.Ising.lpTwoGhost_pinnedPartition_eq E J h side

/--
[lpTwoGhost_pinnedExp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_pinnedExp_eq_eq
  [Fintype W]
  [DecidableEq W]
  {E : Finset (Sym2 W)}
-- given
  (J : Sym2 W -> Real)
  (h : W -> Real)
  (side : W -> Bool)
  (F : ConfigSpace W -> Real) :
-- imply
  (∑ tau : ConfigSpace W, F tau * wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side) (fun _ => 0) (lpTwoGhostPinnedConfig tau)) / (∑ tau : ConfigSpace W, wJ (lpTwoGhostEdges E side) (lpTwoGhostCoupling J h side) (fun _ => 0) (lpTwoGhostPinnedConfig tau)) = expJ E J (lpTwoGhostMixedField h side) F := by
-- proof
  apply StatMech.Ising.lpTwoGhost_pinnedExp_eq E J h side F

/--
[lpTwoGhost_replicaMixedField_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_replicaMixedField_inl_eq
  [Fintype W]
  [DecidableEq W]
  {x : V}
-- given
  (hf : V -> Real) :
-- imply
  lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide (.inl x) = hf x := by
-- proof
  apply StatMech.Ising.lpTwoGhost_replicaMixedField_inl hf x

/--
[lpTwoGhost_replicaMixedField_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_replicaMixedField_inr_eq
  [Fintype W]
  [DecidableEq W]
  {x : V}
-- given
  (hf : V -> Real) :
-- imply
  lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide (.inr x) = -hf x := by
-- proof
  apply StatMech.Ising.lpTwoGhost_replicaMixedField_inr hf x

/--
[lpTwoGhost_replicaMixedField_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpTwoGhost_replicaMixedField_eq_eq
  [Fintype W]
  [DecidableEq W]
-- given
  (hf : V -> Real) :
-- imply
  lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide = Sum.elim hf (fun x => -hf x) := by
-- proof
  apply StatMech.Ising.lpTwoGhost_replicaMixedField_eq hf

/--
[lpReplicaMixedField_nonneg_iff_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostPinned.lean)
-/
@[path]
private lemma lpReplicaMixedField_nonneg_iff_zero_eq
  [Fintype W]
  [DecidableEq W]
-- given
  (hf : V -> Real)
  (hhf : forall x, 0 <= hf x) :
-- imply
  (forall w, 0 <= lpTwoGhostMixedField (lpReplicaFieldMagnitude hf) lpReplicaSide w) <-> forall x, hf x = 0 := by
-- proof
  apply StatMech.Ising.lpReplicaMixedField_nonneg_iff_zero hf hhf


-- created on 2026-10-23
