import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
import Lemma.List.All.of.All.IsChain.Ne
import Lemma.Nat.NotChamberAdjacent
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
open scoped Classical


/--
[coxeterComplex_facet_generator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterFolding.lean)
-/
@[path]
lemma coxeterComplex_facet_generator
  [DecidableEq V]
  {K : ChamberComplex V}
  {B_idx : Type}
  {M : CoxeterMatrix B_idx}
  {φ : Finset V → M.Group}
  {F C : Finset V}
-- given
  (hinj : ∀ C, K.toSimplicialComplex.IsMaximal C → ∀ D, K.toSimplicialComplex.IsMaximal D → φ C = φ D → C = D)
  (hsurj : ∀ w : M.Group, ∃ C, K.toSimplicialComplex.IsMaximal C ∧ φ C = w)
  (hadj_fwd : ∀ C C', K.toSimplicialComplex.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
  (hadj_bwd : ∀ C C', K.toSimplicialComplex.IsMaximal C → K.toSimplicialComplex.IsMaximal C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C') → K.toSimplicialComplex.Adjacent C C')
  (hfacet_shared : ∀ F C, K.toSimplicialComplex.IsFacet F C → K.toSimplicialComplex.IsMaximal C → ∃ D, D ≠ C ∧ K.toSimplicialComplex.IsMaximal D ∧ K.toSimplicialComplex.IsFacet F D)
  (hFC : K.toSimplicialComplex.IsFacet F C)
  (hC : K.toSimplicialComplex.IsMaximal C) :
-- imply
  ∃ i : B_idx, ∀ D, K.toSimplicialComplex.IsMaximal D → φ D = φ C * M.toCoxeterSystem.simple i → K.toSimplicialComplex.IsFacet F D := by
-- proof
  obtain ⟨D₀, hD₀_ne, hD₀_max, hFD₀⟩ := hfacet_shared F C hFC hC
  have hAdj : K.toSimplicialComplex.Adjacent C D₀ :=
    ⟨hC, hD₀_max, hD₀_ne.symm, F, hFC, hFD₀⟩
  have hCA := hadj_fwd C D₀ hAdj
  obtain ⟨_, i, hi⟩ := hCA
  exact ⟨i, fun D hD_max hφD => by
    have hφ_eq : φ D = φ D₀ := by rw [hφD, hi]
    have hD_eq : D = D₀ := hinj D hD_max D₀ hD₀_max hφ_eq
    rw [hD_eq]
    exact hFD₀⟩


-- created on 2026-10-24
