import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.VertexActionHelper
open ChamberComplex
open scoped Classical


/--
[wallReflection_maps_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/VertexActionHelper.lean)
-/
@[path]
lemma wallReflection_maps_chamber
  [DecidableEq V]
  {X : ChamberComplex V}
  {wr : WallReflection X}
  {C D : Finset V}
-- given
  (hDmax : X.toSimplicialComplex.IsMaximal D)
  (hfC : C.image wr.rf.f.morph.toFun = C)
  (hfD : D.image wr.rf.f.morph.toFun = C)
  (hne : C ≠ D) :
-- imply
  D.image wr.refl = C := by
-- proof
  have hfD_ne : D.image wr.rf.f.morph.toFun ≠ D := by
    intro h; rw [hfD] at h; exact hne h
  rw [finset_image_eq_of_agree (Finset.Subset.refl D)
    (wallReflection_eq_f_on_moved wr hDmax hfD_ne)]
  exact hfD


private lemma finset_image_eq_of_agree_eq
  [DecidableEq V]
  {s E : Finset V}
  {r f : V → V}
-- given
  (hsE : s ⊆ E)
  (heq : ∀ v ∈ E, r v = f v) :
-- imply
  s.image r = s.image f := by
-- proof
  apply ChamberComplex.finset_image_eq_of_agree hsE heq

private lemma wallReflection_eq_g_on_fixed_eq
  [DecidableEq V]
  {X : ChamberComplex V}
  {wr : WallReflection X}
  {E : Finset V}
-- given
  (hfE : E.image wr.rf.f.morph.toFun = E) :
-- imply
  ∀ v ∈ E, wr.refl v = wr.rf.g.morph.toFun v := by
-- proof
  apply ChamberComplex.wallReflection_eq_g_on_fixed wr hfE

private lemma wallReflection_eq_f_on_moved_eq
  [DecidableEq V]
  {X : ChamberComplex V}
  {wr : WallReflection X}
  {E : Finset V}
-- given
  (hEmax : X.toSimplicialComplex.IsMaximal E)
  (hfE : E.image wr.rf.f.morph.toFun ≠ E) :
-- imply
  ∀ v ∈ E, wr.refl v = wr.rf.f.morph.toFun v := by
-- proof
  apply ChamberComplex.wallReflection_eq_f_on_moved wr hEmax hfE

private lemma wallReflection_maps_faces_eq
  [DecidableEq V]
  {X : ChamberComplex V}
  {wr : WallReflection X}
  {s : Finset V}
-- given
  (hs : s ∈ X.toSimplicialComplex.faces) :
-- imply
  s.image wr.refl ∈ X.toSimplicialComplex.faces := by
-- proof
  apply ChamberComplex.wallReflection_maps_faces wr s hs

private lemma list_comp_bijective_eq
  [DecidableEq V] :
-- imply
  ∀ (fs : List (V → V)), (∀ f ∈ fs, Function.Bijective f) → Function.Bijective (fs.foldr (· ∘ ·) id) := by
-- proof
  apply ChamberComplex.list_comp_bijective

private lemma chain_compose_eq
  [DecidableEq V]
  {faces : Set (Finset V)}
  {R : Finset V → Finset V → Prop}
  {l : List (Finset V)}
-- given
  (hchain : List.IsChain R l)
  (hmaps : ∀ x y, R x y → ∃ φ : V → V, Function.Bijective φ ∧ (∀ s ∈ faces, s.image φ ∈ faces) ∧ (∀ s, s.image φ ∈ faces → s ∈ faces) ∧ x.image φ = y) :
-- imply
  ∀ (hne : l ≠ []), ∃ φ : V → V, Function.Bijective φ ∧ (∀ s ∈ faces, s.image φ ∈ faces) ∧ (∀ s, s.image φ ∈ faces → s ∈ faces) ∧ (l.head hne).image φ = l.getLast hne := by
-- proof
  apply ChamberComplex.chain_compose l hchain hmaps

private lemma apt_vertex_level_automorphism_eq
  [DecidableEq V]
  {A : SimplicialComplex V}
  {cc : ChamberComplex V}
  {C D : Finset V}
-- given
  (hcc : cc.toSimplicialComplex = A)
  (hWR : ∀ C D : Finset V, A.Adjacent C D → ∃ wr : WallReflection cc, D.image wr.refl = C)
  (hC : A.IsMaximal C)
  (hD : A.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧ D.image φ = C := by
-- proof
  apply ChamberComplex.apt_vertex_level_automorphism A cc hcc hWR C D hC hD


-- created on 2026-10-24
