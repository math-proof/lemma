import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.UniquenessBook
open ChamberComplex
open scoped Classical


namespace ChamberComplex

/--
[imageGalleryStutters_iff_galleryStuttersUnder](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/UniquenessBook.lean)
-/
@[path]
lemma imageGalleryStutters_iff_galleryStuttersUnder
  [DecidableEq V]
  {K : ChamberComplex V}
  {f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex}
  {cs : List (Finset V)} :
-- imply
  ImageGalleryStutters f cs ↔ SimplicialComplex.GalleryStuttersUnder cs f.toFun := by
-- proof
  unfold ImageGalleryStutters SimplicialComplex.GalleryStuttersUnder
  constructor
  · rintro ⟨i, hi, heq⟩
    rw [List.isChain_iff_getElem]
    push Not
    refine ⟨i, by simp only [List.length_map]; exact hi, ?_⟩
    simp only [List.getElem_map]
    exact heq
  · intro hstut
    obtain ⟨n, hn, hne⟩ := List.exists_not_getElem_of_not_isChain hstut
    simp only [List.getElem_map, List.length_map, not_ne_iff] at hn hne
    exact ⟨n, hn, hne⟩

end ChamberComplex

namespace ChamberComplex

/--
[uniqueness_lemma_book](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/UniquenessBook.lean)
-/
@[path]
lemma uniqueness_lemma_book
  [DecidableEq V]
  {K : ChamberComplex V}
  {f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex}
  {C₀ : Finset V}
  {γ : Gallery K.toSimplicialComplex}
-- given
  (hThin : K.IsThin)
  (hfCM : f.IsChamberMap)
  (_hC₀ : K.toSimplicialComplex.IsMaximal C₀)
  (hfix₀ : FixesPointwise f C₀)
  (hstart : γ.chambers.head? = some C₀) :
-- imply
  ImageGalleryStutters f γ.chambers ∨ (∀ C ∈ γ.chambers, FixesPointwise f C) := by
-- proof
  have h := SimplicialComplex.uniqueness_lemma hThin f hfCM C₀ _hC₀ hfix₀ γ hstart
  obtain hstut | hfix := h
  · left
    rwa [imageGalleryStutters_iff_galleryStuttersUnder]
  · right
    intro C hC v hv
    exact hfix C hC v hv

end ChamberComplex


-- created on 2026-10-23
