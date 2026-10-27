import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.Link
open SimplicialComplex
open scoped Classical


/--
[linkComplex_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Link.lean)
-/
@[path]
lemma linkComplex_disjoint
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ : τ ∈ (K.linkComplex σ hσ).faces) :
-- imply
  Disjoint σ τ :=
-- proof
  hτ.2.1


private lemma linkComplex_union_mem
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ : τ ∈ (K.linkComplex σ hσ).faces) :
-- imply
  σ ∪ τ ∈ K.faces :=
-- proof
  hτ.2.2


private lemma linkComplex_face_mem_faces
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ : τ ∈ (K.linkComplex σ hσ).faces) :
-- imply
  τ ∈ K.faces := by
-- proof
  have h_union := linkComplex_union_mem K σ hσ τ hτ
  have h_ne := (K.linkComplex σ hσ).nonempty_of_mem τ hτ
  exact K.down_closed h_union Finset.subset_union_right h_ne


private lemma mem_linkComplex_iff_eq
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces) :
-- imply
  τ ∈ (K.linkComplex σ hσ).faces ↔ τ.Nonempty ∧ Disjoint σ τ ∧ (σ ∪ τ) ∈ K.faces := by
-- proof
  apply SimplicialComplex.mem_linkComplex_iff K σ hσ τ

private lemma mem_linkComplex_of_sdiff_eq
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {w : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hw : w ∈ K.faces)
  (hσw : σ ⊆ w)
  (hne : (w \ σ).Nonempty) :
-- imply
  (w \ σ) ∈ (K.linkComplex σ hσ).faces := by
-- proof
  apply SimplicialComplex.mem_linkComplex_of_sdiff K σ hσ w hw hσw hne


-- created on 2026-10-24
