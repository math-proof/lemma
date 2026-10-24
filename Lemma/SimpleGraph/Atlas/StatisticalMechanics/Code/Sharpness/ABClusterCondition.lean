import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.ABClusterCondition
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[abcc_connEvent_singleton_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_connEvent_singleton_symm_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {omega : ConfigSpace (Sym2 W)}
  {a b : W} :
-- imply
  omega ∈ connEvent H Set.univ a {b} ↔ omega ∈ connEvent H Set.univ b {a} := by
-- proof
  apply StatMech.Sharpness.abcc_connEvent_singleton_symm H omega a b

/--
[abcc_restricted_iff_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_restricted_iff_blocked_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {omega : ConfigSpace (Sym2 W)}
  {u x g : W} :
-- imply
  omega ∈ connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ ↔ g ∈ mpiBlockedSet H {u} omega ∧ x ∉ mpiBlockedSet H {u} omega := by
-- proof
  apply StatMech.Sharpness.abcc_restricted_iff_blocked H omega u x g

/--
[abcc_probV_surface_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_probV_surface_partition_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {B : Set W}
  [DecidablePred P]
  {C : Set (ConfigSpace (Sym2 W))}
-- given
  (P : Finset W → Prop) :
-- imply
  probV p ({omega | P (mpiBlockedSet H B omega)} ∩ C) = ∑ S ∈ (Finset.univ.filter P), probV p (mpiSurfaceEvent H B S ∩ C) := by
-- proof
  apply StatMech.Sharpness.abcc_probV_surface_partition H p B P C

/--
[abcc_conn_inside_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_conn_inside_blocked_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {B : Set W}
  {S : Finset W}
  {omega : ConfigSpace (Sym2 W)}
  {y g : W}
-- given
  (hS : mpiBlockedSet H B omega = S)
  (hgS : g ∈ S)
  (hyg : omega ∈ connEvent H Set.univ y {g}) :
-- imply
  omega ∈ connEvent H (S : Set W) y {g} := by
-- proof
  apply StatMech.Sharpness.abcc_conn_inside_blocked H B S omega hS y g hgS hyg

/--
[abcc_conn_surface_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_conn_surface_factor_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {B : Set W}
  {S : Finset W}
  {y g : W} :
-- imply
  probV p (connEvent H (S : Set W) y {g} ∩ mpiSurfaceEvent H B S) = probV p (connEvent H (S : Set W) y {g}) * probV p (mpiSurfaceEvent H B S) := by
-- proof
  apply StatMech.Sharpness.abcc_conn_surface_factor H p B S y g

/--
[abcc_conn_surface_factor_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_conn_surface_factor_set_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {B : Set W}
  {S : Finset W}
  {y : W}
  {T : Set W} :
-- imply
  probV p (connEvent H (S : Set W) y T ∩ mpiSurfaceEvent H B S) = probV p (connEvent H (S : Set W) y T) * probV p (mpiSurfaceEvent H B S) := by
-- proof
  apply StatMech.Sharpness.abcc_conn_surface_factor_set H p B S y T

/--
[abcc_surface_inter_conn_eq_inside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_surface_inter_conn_eq_inside_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {B : Set W}
  {S : Finset W}
  {g y : W}
-- given
  (hgS : g ∈ S) :
-- imply
  mpiSurfaceEvent H B S ∩ connEvent H Set.univ y {g} = mpiSurfaceEvent H B S ∩ connEvent H (S : Set W) y {g} := by
-- proof
  apply StatMech.Sharpness.abcc_surface_inter_conn_eq_inside H B S g y hgS

/--
[abcc_surface_inter_conn_eq_inside_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_surface_inter_conn_eq_inside_set_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {B : Set W}
  {S : Finset W}
  {T : Set W}
  {y : W}
-- given
  (hTS : T ⊆ (S : Set W)) :
-- imply
  mpiSurfaceEvent H B S ∩ connEvent H Set.univ y T = mpiSurfaceEvent H B S ∩ connEvent H (S : Set W) y T := by
-- proof
  apply StatMech.Sharpness.abcc_surface_inter_conn_eq_inside_set H B S T y hTS

/--
[abcc_conn_inside_subset_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_conn_inside_subset_global_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {S : Finset W}
  {y g : W} :
-- imply
  connEvent H (S : Set W) y {g} ⊆ connEvent H Set.univ y {g} := by
-- proof
  apply StatMech.Sharpness.abcc_conn_inside_subset_global H S y g

/--
[abcc_conn_inside_set_subset_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_conn_inside_set_subset_global_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {S : Finset W}
  {y : W}
  {T : Set W} :
-- imply
  connEvent H (S : Set W) y T ⊆ connEvent H Set.univ y T := by
-- proof
  apply StatMech.Sharpness.abcc_conn_inside_set_subset_global H S y T

/--
[abcc_cluster_conditioning_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_cluster_conditioning_set_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {u x y : W}
  {T : Set W}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  probV p ((connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u T)ᶜ) ∩ connEvent H Set.univ y T) ≤ probV p (connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u T)ᶜ) * probV p (connEvent H Set.univ y T) := by
-- proof
  apply StatMech.Sharpness.abcc_cluster_conditioning_set H p hp u x y T

/--
[abcc_cluster_conditioning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_cluster_conditioning_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {u x y g : W}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  probV p ((connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) ∩ connEvent H Set.univ y {g}) ≤ probV p (connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) * probV p (connEvent H Set.univ y {g}) := by
-- proof
  apply StatMech.Sharpness.abcc_cluster_conditioning H p hp u x y g

/--
[abcc_closedPivotal_le_products](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_closedPivotal_le_products_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {u x y g : W}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  probV p (abgiClosedPivotal s(x, y) (connEvent H Set.univ u {g})) ≤ probV p (connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u {g})ᶜ) * probV p (connEvent H Set.univ y {g}) + probV p (connEvent H Set.univ u {y} ∩ (connEvent H Set.univ u {g})ᶜ) * probV p (connEvent H Set.univ x {g}) := by
-- proof
  apply StatMech.Sharpness.abcc_closedPivotal_le_products H p hp u x y g

/--
[abcc_closedPivotal_le_products_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABClusterCondition.lean)
-/
@[path]
private lemma abcc_closedPivotal_le_products_set_eq
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {p : Sym2 W → ℝ}
  {u x y : W}
  {T : Set W}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  probV p (abgiClosedPivotal s(x, y) (connEvent H Set.univ u T)) ≤ probV p (connEvent H Set.univ u {x} ∩ (connEvent H Set.univ u T)ᶜ) * probV p (connEvent H Set.univ y T) + probV p (connEvent H Set.univ u {y} ∩ (connEvent H Set.univ u T)ᶜ) * probV p (connEvent H Set.univ x T) := by
-- proof
  apply StatMech.Sharpness.abcc_closedPivotal_le_products_set H p hp u x y T


-- created on 2026-10-23
