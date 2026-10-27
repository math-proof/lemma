import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.MorphismDefinitions
open PrimeSpectrum MorphismDefinitions


namespace MorphismDefinitions

/--
[isFiniteAlgebra_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean)
-/
@[path]
lemma isFiniteAlgebra_isIntegral
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A] :
-- imply
  Algebra.IsIntegral B A :=
-- proof
  Algebra.IsIntegral.of_finite B A

end MorphismDefinitions

namespace MorphismDefinitions

/--
[finite_morphism_isClosedMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean)
-/
@[path]
lemma finite_morphism_isClosedMap
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A] :
-- imply
  IsClosedMap (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  have hIntegral : (algebraMap B A).IsIntegral := fun x =>
    (Algebra.IsIntegral.of_finite B A).isIntegral x
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap B A) hIntegral

end MorphismDefinitions

namespace MorphismDefinitions

/--
[finite_morphism_finite_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean)
-/
@[path]
lemma finite_morphism_finite_fibers
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
  {𝔭 : PrimeSpectrum B} :
-- imply
  Set.Finite (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {𝔭}) :=
-- proof
  Algebra.QuasiFinite.finite_comap_preimage_singleton 𝔭

end MorphismDefinitions

namespace MorphismDefinitions

/--
[finite_morphism_surjective_on_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean)
-/
@[path]
lemma finite_morphism_surjective_on_spec
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  have hIntegral : (algebraMap B A).IsIntegral := fun x =>
    (Algebra.IsIntegral.of_finite B A).isIntegral x
  exact hIntegral.comap_surjective hinj

end MorphismDefinitions

namespace MorphismDefinitions

/--
[finite_morphism_fiber_finite_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean)
-/
@[path]
lemma finite_morphism_fiber_finite_nonempty
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
  {𝔭 : PrimeSpectrum B}
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {𝔭}).Finite ∧ (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {𝔭}).Nonempty := by
-- proof
  refine ⟨finite_morphism_finite_fibers 𝔭, ?_⟩
  obtain ⟨q, hq⟩ := finite_morphism_surjective_on_spec hinj 𝔭
  exact ⟨q, hq ▸ Set.mem_preimage.mpr rfl⟩

end MorphismDefinitions

namespace MorphismDefinitions

/--
[finite_morphism_dim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismDefinitions.lean)
-/
@[path]
lemma finite_morphism_dim_eq
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  ringKrullDim A = ringKrullDim B :=
-- proof
  FiniteMorphismDimension.ringKrullDim_eq_of_injective_finite hinj

end MorphismDefinitions


-- created on 2026-10-23
