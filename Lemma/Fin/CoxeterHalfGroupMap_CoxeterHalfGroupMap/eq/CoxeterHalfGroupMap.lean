import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterFoldingHelpers
open ChamberComplex
open scoped Classical


/--
[coxeterHalfGroupMap_idempotent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterFoldingHelpers.lean)
-/
@[path]
private lemma main
  [DecidableEq V]
  {M : CoxeterMatrix B_idx}
  {i : B_idx}
  {w : M.Group} :
-- imply
  coxeterHalfGroupMap M i (coxeterHalfGroupMap M i w) = coxeterHalfGroupMap M i w := by
-- proof
  unfold coxeterHalfGroupMap
  simp only
  set cs := M.toCoxeterSystem
  set s := cs.simple i
  by_cases h1 : cs.length (s * w) > cs.length w
  · simp only [h1, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    rw [cs.simple_mul_simple_cancel_left i]
    have hne := cs.length_simple_mul_ne w i
    have hlt : cs.length (s * w) < cs.length w :=
      lt_of_le_of_ne (Nat.not_lt.mp h1) hne
    simp only [show cs.length w > cs.length (s * w) from hlt, ↓reduceIte]



/--
[coxeterHalfChamberMap_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterFoldingHelpers.lean)
-/
private lemma coxeterHalfChamberMap_spec
  [DecidableEq V]
  {K : ChamberComplex V}
  {M : CoxeterMatrix B_idx}
  {φ : Finset V → M.Group}
  {i : B_idx}
  {E : Finset V}
-- given
  (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w) :
-- imply
  φ (coxeterHalfChamberMap K M φ hsurj i E) = coxeterHalfGroupMap M i (φ E) := by
-- proof
  unfold coxeterHalfChamberMap coxeterHalfGroupMap
  simp only
  split_ifs with h
  · rfl
  · exact (hsurj (M.toCoxeterSystem.simple i * φ E)).choose_spec.2



/--
[coxeterHalfChamberMap_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterFoldingHelpers.lean)
-/
private lemma coxeterHalfChamberMap_maximal
  [DecidableEq V]
  {K : ChamberComplex V}
  {M : CoxeterMatrix B_idx}
  {φ : Finset V → M.Group}
  {i : B_idx}
  {E : Finset V}
-- given
  (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
  (hE : K.toSimplicialComplex.IsMaximal E) :
-- imply
  K.toSimplicialComplex.IsMaximal (coxeterHalfChamberMap K M φ hsurj i E) := by
-- proof
  unfold coxeterHalfChamberMap
  simp only
  split_ifs with h
  · exact hE
  · exact (hsurj (M.toCoxeterSystem.simple i * φ E)).choose_spec.1



-- created on 2026-10-23
-- updated on 2026-10-24
