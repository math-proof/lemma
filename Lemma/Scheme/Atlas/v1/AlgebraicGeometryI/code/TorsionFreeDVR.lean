import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.TorsionFreeDVR


/--
[dvr_fg_torsionFree_is_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionFreeDVR.lean)
-/
@[path]
lemma dvr_fg_torsionFree_is_free
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [Module.IsTorsionFree R M] :
-- imply
  Module.Free R M :=
-- proof
  inferInstance

/--
[dvr_torsionSplitting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionFreeDVR.lean)
-/
@[path]
lemma dvr_torsionSplitting
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  Nonempty ((↥(Submodule.torsion R M) × (M ⧸ Submodule.torsion R M)) ≃ₗ[R] M) := by
-- proof
  have : Module.IsTorsionFree R (M ⧸ Submodule.torsion R M) := inferInstance
  have : Module.Free R (M ⧸ Submodule.torsion R M) := inferInstance
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _
    LinearMap.id (Submodule.torsion R M).mkQ_surjective
  exact ⟨lequivProdOfRightSplitExact (Submodule.torsion R M).injective_subtype
    (by simp [Submodule.range_subtype, Submodule.ker_mkQ]) hf⟩
universe u v

/--
[dvr_fg_structure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionFreeDVR.lean)
-/
@[path]
lemma dvr_fg_structure
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {M : Type v}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible (p i)) (e : ι → ℕ), Nonempty (M ≃ₗ[R] (Fin n →₀ R) × DirectSum ι fun i => R ⧸ R ∙ p i ^ e i) :=
-- proof
  Module.equiv_free_prod_directSum R M

/--
[dvr_quotient_torsion_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionFreeDVR.lean)
-/
@[path]
lemma dvr_quotient_torsion_free
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  Module.Free R (M ⧸ Submodule.torsion R M) :=
-- proof
  inferInstance

/--
[dvr_free_iff_torsionFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionFreeDVR.lean)
-/
@[path]
lemma dvr_free_iff_torsionFree
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M] :
-- imply
  Module.Free R M ↔ Module.IsTorsionFree R M :=
-- proof
  Module.free_iff_isTorsionFree


-- created on 2026-10-23
