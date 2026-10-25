import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.npjnopinch.Part2
open SimpleGraph Set StatMech StatMech.Walls


/--
[npj_lift_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_lift_walk_eq
  {S : Set (Site 2)}
  {x y : S}
  {p : ((hypercubicLattice 2).induce S).Walk x y} :
-- imply
  ∃ w : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2), ∀ z ∈ w.support, z ∈ S := by
-- proof
  apply StatMech.Walls.npj_lift_walk S p

/--
[npj_ambient_walk_of_induce_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_ambient_walk_of_induce_reachable_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S)
  (h : ((hypercubicLattice 2).induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
-- imply
  ∃ w : (hypercubicLattice 2).Walk x y, ∀ z ∈ w.support, z ∈ S := by
-- proof
  apply StatMech.Walls.npj_ambient_walk_of_induce_reachable hx hy h

/--
[npj_paths_of_diagSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_paths_of_diagSplit_eq
  {K : Set (Site 2)}
  {a b : ℤ}
-- given
  (hK : ((hypercubicLattice 2).induce K).Connected)
  (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
  (h00 : npj_c00 a b ∈ K)
  (h11 : npj_c11 a b ∈ K)
  (h10 : npj_c10 a b ∈ (Kᶜ : Set (Site 2)))
  (h01 : npj_c01 a b ∈ (Kᶜ : Set (Site 2))) :
-- imply
  (∃ w : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b), ∀ z ∈ w.support, z ∈ K) ∧ (∃ w : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b), ∀ z ∈ w.support, z ∈ (Kᶜ : Set (Site 2))) := by
-- proof
  apply StatMech.Walls.npj_paths_of_diagSplit a b hK hKc h00 h11 h10 h01

/--
[npj_noPinch_primary_of_separatingSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_noPinch_primary_of_separatingSide_eq
  {K : Set (Site 2)}
  {a b : ℤ}
  {wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b)}
  {wKc : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b)}
-- given
  (hwK : ∀ z ∈ wK.support, z ∈ K)
  (hwKc : ∀ z ∈ wKc.support, z ∈ (Kᶜ : Set (Site 2)))
  (hsep : jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support} {npj_c10 a b} {npj_c01 a b}) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.npj_noPinch_primary_of_separatingSide a b hwK hwKc hsep

/--
[npj_noPinch_of_separatingSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_noPinch_of_separatingSides_eq
  {K : Set (Site 2)}
-- given
  (hK : ((hypercubicLattice 2).induce K).Connected)
  (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
  (hres : ∀ (a b : ℤ), (npj_c00 a b ∈ K → npj_c11 a b ∈ K → npj_c10 a b ∈ (Kᶜ : Set (Site 2)) → npj_c01 a b ∈ (Kᶜ : Set (Site 2)) → ∀ wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b), (∀ z ∈ wK.support, z ∈ K) → npj_SeparatingSideResidue a b wK) ∧ (npj_c10 a b ∈ K → npj_c01 a b ∈ K → npj_c00 a b ∈ (Kᶜ : Set (Site 2)) → npj_c11 a b ∈ (Kᶜ : Set (Site 2)) → ∀ wK : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b), (∀ z ∈ wK.support, z ∈ K) → jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support} {npj_c00 a b} {npj_c11 a b})) :
-- imply
  dg2_NoPinch K := by
-- proof
  apply StatMech.Walls.npj_noPinch_of_separatingSides hK hKc hres

/--
[npj_jed_faceCut_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_jed_faceCut_even_eq
  {v : Site 2}
-- given
  (T : Site 2 → Prop) :
-- imply
  Even (jce_degree (jed_cutSet T) v) := by
-- proof
  apply StatMech.Walls.npj_jed_faceCut_even T v

/--
[npj_jed_faceSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_jed_faceSeparation_eq
  {H : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
-- given
  (hfin : H.edgeSet.Finite)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Walls.npj_jed_faceSeparation H hfin p q f0 g0 hpq hnpq hfg hshared hsep

/--
[npj_jed_mismatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_jed_mismatch_eq :
-- imply
  (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧ (∀ (H : SimpleGraph (Site 2)), H.edgeSet.Finite → ∀ (p q f0 g0 : Site 2), (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet → (hypercubicLattice 2).Adj f0 g0 → sharedPrimalEdge f0 g0 = s(p, q) → ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 → H.Reachable p q) ∧ (∀ {K : Set (Site 2)}, ((hypercubicLattice 2).induce K).Connected → ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected → (∀ (a b : ℤ), (npj_c00 a b ∈ K → npj_c11 a b ∈ K → npj_c10 a b ∈ (Kᶜ : Set (Site 2)) → npj_c01 a b ∈ (Kᶜ : Set (Site 2)) → ∀ wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b), (∀ z ∈ wK.support, z ∈ K) → npj_SeparatingSideResidue a b wK) ∧ (npj_c10 a b ∈ K → npj_c01 a b ∈ K → npj_c00 a b ∈ (Kᶜ : Set (Site 2)) → npj_c11 a b ∈ (Kᶜ : Set (Site 2)) → ∀ wK : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b), (∀ z ∈ wK.support, z ∈ K) → jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support} {npj_c00 a b} {npj_c11 a b})) → dg2_NoPinch K) := by
-- proof
  apply StatMech.Walls.npj_jed_mismatch

/--
[npj_pinch_no_origin_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_pinch_no_origin_neighbour_eq
  {w : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj (npj_c00 0 0) w) :
-- imply
  w ∉ dg2_pinchSet := by
-- proof
  apply StatMech.Walls.npj_pinch_no_origin_neighbour hadj

/--
[npj_pinch_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_pinch_consistent_eq :
-- imply
  ¬ ∃ w : (hypercubicLattice 2).Walk (npj_c00 0 0) (npj_c11 0 0), ∀ z ∈ w.support, z ∈ dg2_pinchSet := by
-- proof
  apply StatMech.Walls.npj_pinch_consistent

/--
[npj_box_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_box_noPinch_eq
  {x0 x1 y0 y1 : ℤ} :
-- imply
  dg2_NoPinch {p : Site 2 | x0 ≤ p 0 ∧ p 0 ≤ x1 ∧ y0 ≤ p 1 ∧ p 1 ≤ y1} := by
-- proof
  apply StatMech.Walls.npj_box_noPinch x0 x1 y0 y1

/--
[npj_extraction_applicable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_extraction_applicable_eq
  {K : Set (Site 2)}
  {a b : ℤ}
-- given
  (hK : ((hypercubicLattice 2).induce K).Connected)
  (hKc : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected)
  (h00 : npj_c00 a b ∈ K)
  (h11 : npj_c11 a b ∈ K)
  (h10 : npj_c10 a b ∈ (Kᶜ : Set (Site 2)))
  (h01 : npj_c01 a b ∈ (Kᶜ : Set (Site 2))) :
-- imply
  (∃ w : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b), ∀ z ∈ w.support, z ∈ K) ∧ (∃ w : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b), ∀ z ∈ w.support, z ∈ (Kᶜ : Set (Site 2))) := by
-- proof
  apply StatMech.Walls.npj_extraction_applicable a b hK hKc h00 h11 h10 h01

/--
[npj_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/npjnopinch.lean)
-/
@[path]
private lemma npj_status_eq :
-- imply
  (∀ {K : Set (Site 2)}, ((hypercubicLattice 2).induce K).Connected → ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Connected → (∀ (a b : ℤ), (npj_c00 a b ∈ K → npj_c11 a b ∈ K → npj_c10 a b ∈ (Kᶜ : Set (Site 2)) → npj_c01 a b ∈ (Kᶜ : Set (Site 2)) → ∀ wK : (hypercubicLattice 2).Walk (npj_c00 a b) (npj_c11 a b), (∀ z ∈ wK.support, z ∈ K) → npj_SeparatingSideResidue a b wK) ∧ (npj_c10 a b ∈ K → npj_c01 a b ∈ K → npj_c00 a b ∈ (Kᶜ : Set (Site 2)) → npj_c11 a b ∈ (Kᶜ : Set (Site 2)) → ∀ wK : (hypercubicLattice 2).Walk (npj_c10 a b) (npj_c01 a b), (∀ z ∈ wK.support, z ∈ K) → jcu_HasSeparatingSide Set.univ {z | z ∈ wK.support} {npj_c00 a b} {npj_c11 a b})) → dg2_NoPinch K) ∧ (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧ (¬ ∃ w : (hypercubicLattice 2).Walk (npj_c00 0 0) (npj_c11 0 0), ∀ z ∈ w.support, z ∈ dg2_pinchSet) := by
-- proof
  apply StatMech.Walls.npj_status


-- created on 2026-10-23
