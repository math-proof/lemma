import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostInfluence
open Finset Set SimpleGraph StatMech StatMech.Sharpness


/--
[abgi_probV_closedPivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_probV_closedPivotal_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
  {e : E} :
-- imply
  probV p (abgiClosedPivotal e A) = (1 - p e) * pivotalProbV p A e := by
-- proof
  apply StatMech.Sharpness.abgi_probV_closedPivotal p A e

/--
[abgi_probV_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_probV_mono_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
  (hAB : A ⊆ B) :
-- imply
  probV p A ≤ probV p B := by
-- proof
  apply StatMech.Sharpness.abgi_probV_mono p hp hAB

/--
[abgi_probV_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_probV_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  0 ≤ probV p A := by
-- proof
  apply StatMech.Sharpness.abgi_probV_nonneg p hp A

/--
[abgi_probV_union_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_probV_union_le_eq
  [Fintype E]
  [DecidableEq E]
  {p : E → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) :
-- imply
  probV p (A ∪ B) ≤ probV p A + probV p B := by
-- proof
  apply StatMech.Sharpness.abgi_probV_union_le p hp A B

/--
[abgi_closedPivotal_conn_subset_oriented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_closedPivotal_conn_subset_oriented_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {H : SimpleGraph W}
  {D : Set W}
  {u : W}
  {B : Set W}
  {x y : W}
-- given
  (hu : u ∈ D)
  (hx : x ∈ D)
  (hy : y ∈ D) :
-- imply
  abgiClosedPivotal s(x, y) (connEvent H D u B) ⊆ ((connEvent H D u {x} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D y B) ∪ ((connEvent H D u {y} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D x B) := by
-- proof
  apply StatMech.Sharpness.abgi_closedPivotal_conn_subset_oriented H D u B x y hu hx hy

/--
[abgi_probV_closedPivotal_conn_le_oriented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_probV_closedPivotal_conn_le_oriented_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  {p : Sym2 W → ℝ}
  {H : SimpleGraph W}
  {D : Set W}
  {u : W}
  {B : Set W}
  {x y : W}
-- given
  (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
  (hu : u ∈ D)
  (hx : x ∈ D)
  (hy : y ∈ D) :
-- imply
  probV p (abgiClosedPivotal s(x, y) (connEvent H D u B)) ≤ probV p ((connEvent H D u {x} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D y B) + probV p ((connEvent H D u {y} ∩ (connEvent H D u B)ᶜ) ∩ connEvent H D x B) := by
-- proof
  apply StatMech.Sharpness.abgi_probV_closedPivotal_conn_le_oriented p hp H D u B x y hu hx hy

/--
[abgi_closedPivotal_ghost_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_closedPivotal_ghost_eq_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V} :
-- imply
  abgiClosedPivotal s(some x, none) (connEvent (withGhost G) Set.univ (some o) {none}) = connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) {none})ᶜ := by
-- proof
  apply StatMech.Sharpness.abgi_closedPivotal_ghost_eq G o x

/--
[abgi_closedPivotal_ghost_eq_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_closedPivotal_ghost_eq_target_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
  {T : Set (Option V)}
-- given
  (hghost : none ∈ T) :
-- imply
  abgiClosedPivotal s(some x, none) (connEvent (withGhost G) Set.univ (some o) T) = connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) T)ᶜ := by
-- proof
  apply StatMech.Sharpness.abgi_closedPivotal_ghost_eq_target G o x T hghost

/--
[abgi_ghostInfluence_eq_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_ghostInfluence_eq_restricted_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Sym2 (Option V) → ℝ}
  {q : ℝ}
  {o x : V} :
-- imply
  (1 - q) * pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) q p) (connEvent (withGhost G) Set.univ (some o) {none}) s(some x, none) = probV (paramOn (FieldGhostDict.ghostEdges V) q p) (connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) := by
-- proof
  apply StatMech.Sharpness.abgi_ghostInfluence_eq_restricted G p q o x

/--
[abgi_ghostInfluence_exp_eq_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_ghostInfluence_exp_eq_restricted_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Sym2 (Option V) → ℝ}
  {o x : V}
-- given
  (h : ℝ) :
-- imply
  pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p) (connEvent (withGhost G) Set.univ (some o) {none}) s(some x, none) * Real.exp (-h) = probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p) (connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) := by
-- proof
  apply StatMech.Sharpness.abgi_ghostInfluence_exp_eq_restricted G p h o x

/--
[abgi_deriv_field_eq_sum_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_deriv_field_eq_sum_restricted_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Sym2 (Option V) → ℝ}
  {o : V}
-- given
  (h : ℝ) :
-- imply
  deriv (fun t => probV (paramOn (FieldGhostDict.ghostEdges V) (qField t) p) (connEvent (withGhost G) Set.univ (some o) {none})) h = ∑ x : V, probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p) (connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) {none})ᶜ) := by
-- proof
  apply StatMech.Sharpness.abgi_deriv_field_eq_sum_restricted G p h o

/--
[abgi_ghostInfluence_exp_eq_restricted_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_ghostInfluence_exp_eq_restricted_target_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Sym2 (Option V) → ℝ}
  {o x : V}
  {T : Set (Option V)}
-- given
  (h : ℝ)
  (hghost : none ∈ T) :
-- imply
  pivotalProbV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p) (connEvent (withGhost G) Set.univ (some o) T) s(some x, none) * Real.exp (-h) = probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p) (connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) T)ᶜ) := by
-- proof
  apply StatMech.Sharpness.abgi_ghostInfluence_exp_eq_restricted_target G p h o x T hghost

/--
[abgi_deriv_field_eq_sum_restricted_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostInfluence.lean)
-/
@[path]
private lemma abgi_deriv_field_eq_sum_restricted_target_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype W]
  [DecidableEq W]
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : Sym2 (Option V) → ℝ}
  {o : V}
  {T : Set (Option V)}
-- given
  (h : ℝ)
  (hghost : none ∈ T) :
-- imply
  deriv (fun t => probV (paramOn (FieldGhostDict.ghostEdges V) (qField t) p) (connEvent (withGhost G) Set.univ (some o) T)) h = ∑ x : V, probV (paramOn (FieldGhostDict.ghostEdges V) (qField h) p) (connEvent (withGhost G) Set.univ (some o) {some x} ∩ (connEvent (withGhost G) Set.univ (some o) T)ᶜ) := by
-- proof
  apply StatMech.Sharpness.abgi_deriv_field_eq_sum_restricted_target G p h o T hghost


-- created on 2026-10-23
