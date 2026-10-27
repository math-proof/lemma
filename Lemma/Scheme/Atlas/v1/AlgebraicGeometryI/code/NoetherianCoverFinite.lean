import Mathlib
import Initialize.Tactic.Attr.Basic
open TopologicalSpace Set


/--
[noetherian_open_cover_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherianCoverFinite.lean)
-/
@[path]
lemma noetherian_open_cover_finite
  {X : Type*}
  [TopologicalSpace X]
  [NoetherianSpace X]
  {U : Set (Set X)}
-- given
  (hU : ∀ u ∈ U, IsOpen u)
  (hcover : ⋃₀ U = Set.univ) :
-- imply
  ∃ F ⊆ U, F.Finite ∧ ⋃₀ F = Set.univ := by
-- proof
  have hcompact : IsCompact (Set.univ : Set X) := NoetherianSpace.isCompact Set.univ
  rw [sUnion_eq_biUnion] at hcover
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i ∈ U, i := hcover.ge
  obtain ⟨F, hFU, hFfin, hFcover⟩ := hcompact.elim_finite_subcover_image hU hcover'
  refine ⟨F, hFU, hFfin, ?_⟩
  rw [sUnion_eq_biUnion, eq_univ_iff_forall]
  exact fun x => hFcover (mem_univ x)


-- created on 2026-10-23
