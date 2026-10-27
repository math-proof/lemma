import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NoetherNormalization
open MvPolynomial PrimeSpectrum
open AlgebraicGeometry AlgebraicGeometry.Scheme


/--
[noether_normalization_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_integral
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Nontrivial A] :
-- imply
  ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A, Function.Injective g ∧ g.IsIntegral :=
-- proof
  exists_integral_inj_algHom_of_fg k A

/--
[noether_normalization_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_finite
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Nontrivial A] :
-- imply
  ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A, Function.Injective g ∧ g.Finite :=
-- proof
  exists_finite_inj_algHom_of_fg k A

/--
[noether_normalization_spec_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_spec_surjective
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Nontrivial A] :
-- imply
  ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A, Function.Injective g ∧ g.Finite ∧ Function.Surjective (PrimeSpectrum.comap g.toRingHom) := by
-- proof
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  refine ⟨d, g, hinj, hfin, ?_⟩
  have hfin_rh : g.toRingHom.Finite := hfin
  have hint : g.toRingHom.IsIntegral := RingHom.IsIntegral.of_finite hfin_rh
  exact hint.comap_surjective hinj
section ZariskiLemma

/--
[noether_normalization_implies_zariski_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_implies_zariski_lemma
  {k A : Type*}
  [Field k]
  [Field A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  Algebra.IsAlgebraic k A :=
-- proof
  essential_nullstellensatz k A

/--
[zariski_lemma_module_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma zariski_lemma_module_finite
  {k A : Type*}
  [Field k]
  [Field A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  Module.Finite k A :=
-- proof
  finite_of_finiteType_field k A
end ZariskiLemma
section Dimension

/--
[noether_normalization_dimension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_dimension
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Nontrivial A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  ∃ d : ℕ, ∃ g : MvPolynomial (Fin d) k →ₐ[k] A, Function.Injective g ∧ g.Finite ∧ ringKrullDim A = ↑d := by
-- proof
  obtain ⟨d, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  exact ⟨d, g, hinj, hfin, ringKrullDim_eq_of_noetherNormalization d g hinj hfin⟩

/--
[noether_normalization_dim_is_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_dim_is_nat
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Nontrivial A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  ∃ d : ℕ, ringKrullDim A = ↑d :=
-- proof
  ringKrullDim_fg_algebra_eq_nat k A

/--
[dim_preserved_by_finite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma dim_preserved_by_finite_injective
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
end Dimension
section Quotient

/--
[noether_normalization_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NoetherNormalization.lean)
-/
@[path]
lemma noether_normalization_quotient
  [Field k]
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) k)}
-- given
  (hI : I ≠ ⊤) :
-- imply
  ∃ s, s ≤ n ∧ ∃ g : MvPolynomial (Fin s) k →ₐ[k] MvPolynomial (Fin n) k ⧸ I, Function.Injective g ∧ g.IsIntegral := by
-- proof
  obtain ⟨s, hs, g, hinj, hint⟩ := exists_integral_inj_algHom_of_quotient I hI
  exact ⟨s, hs, g, hinj, hint⟩
end Quotient
section AlgebraicVarietyDimension
open AlgebraicGeometry AlgebraicGeometry.Scheme
universe u
/-- An algebraic variety over a field has finite (natural number) Krull dimension as a
topological space. -/
end AlgebraicVarietyDimension


-- created on 2026-10-23
