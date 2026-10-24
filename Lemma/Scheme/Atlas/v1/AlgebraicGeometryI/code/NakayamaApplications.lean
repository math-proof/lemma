import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
open Ideal


/--
[nakayama_determinant_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma nakayama_determinant_form
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {I : Ideal R}
-- given
  (hIM : I • (⊤ : Submodule R M) = ⊤) :
-- imply
  ∃ a : R, a - 1 ∈ I ∧ ∀ m : M, a • m = 0 := by
-- proof
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    I ⊤ Module.Finite.fg_top (ge_of_eq hIM)
  exact ⟨r, hr1, fun m => hr2 m Submodule.mem_top⟩

/--
[nakayama_exists_identity_element](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma nakayama_exists_identity_element
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {I : Ideal R}
-- given
  (hIM : I • (⊤ : Submodule R M) = ⊤) :
-- imply
  ∃ a ∈ I, ∀ m : M, a • m = m := by
-- proof
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul
    I ⊤ Module.Finite.fg_top (ge_of_eq hIM)
  exact ⟨r, hr1, fun m => hr2 m Submodule.mem_top⟩

/--
[nakayama_ne_top_of_le_jacobson](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma nakayama_ne_top_of_le_jacobson
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Nontrivial M]
  [Module.Finite R M]
  {I : Ideal R}
-- given
  (hI : I ≤ jacobson ⊥) :
-- imply
  I • (⊤ : Submodule R M) ≠ ⊤ :=
-- proof
  Ne.symm (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
    (le_trans hI (jacobson_mono bot_le)))

/--
[nakayama_subsingleton_of_le_jacobson](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma nakayama_subsingleton_of_le_jacobson
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {I : Ideal R}
-- given
  (hIM : I • (⊤ : Submodule R M) = ⊤)
  (hIjac : I ≤ jacobson ⊥) :
-- imply
  Subsingleton M := by
-- proof
  have h := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤
    Module.Finite.fg_top (ge_of_eq hIM) hIjac
  have : ∀ x : M, x = 0 := fun x =>
    (Submodule.mem_bot R).mp (h ▸ Submodule.mem_top)
  exact ⟨fun a b => by rw [this a, this b]⟩
section FiniteMorphisms

/--
[finite_morphism_spec_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma finite_morphism_spec_surjective
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
  [FaithfulSMul B A] :
-- imply
  Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  have hInt : (algebraMap B A).IsIntegral := fun x => IsIntegral.of_finite B x
  exact hInt.comap_surjective (FaithfulSMul.algebraMap_injective B A)

/--
[finite_morphism_spec_surjective_of_ringHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma finite_morphism_spec_surjective_of_ringHom
  [CommRing B]
  [CommRing A]
  {f : B →+* A}
-- given
  (hfin : f.Finite)
  (hinj : Function.Injective f) :
-- imply
  Function.Surjective (PrimeSpectrum.comap f) := by
-- proof
  algebraize [f]
  have : Module.Finite B A := hfin
  have hInt : f.IsIntegral := fun x => IsIntegral.of_finite B x
  exact hInt.comap_surjective hinj
end FiniteMorphisms
section Nullstellensatz

/--
[essential_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma essential_nullstellensatz
  {k A : Type*}
  [Field k]
  [Field A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  Algebra.IsAlgebraic k A := by
-- proof
  have : Module.Finite k A := finite_of_finite_type_of_isJacobsonRing k A
  exact Algebra.IsAlgebraic.of_finite k A

/--
[finite_of_finiteType_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NakayamaApplications.lean)
-/
@[path]
lemma finite_of_finiteType_field
  {k A : Type*}
  [Field k]
  [Field A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  Module.Finite k A :=
-- proof
  finite_of_finite_type_of_isJacobsonRing k A
end Nullstellensatz


-- created on 2026-10-23
