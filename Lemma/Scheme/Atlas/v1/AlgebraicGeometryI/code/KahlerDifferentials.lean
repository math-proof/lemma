import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.KahlerDifferentials
open Polynomial KaehlerDifferential Module
open scoped TensorProduct


/--
[kaehlerDifferential_universalProperty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_universalProperty
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [AddCommGroup M]
  [Module R M]
  [Module S M]
  [IsScalarTower R S M] :
-- imply
  Nonempty ((Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M) :=
-- proof
  ⟨KaehlerDifferential.linearMapEquivDerivation R S⟩

/--
[kaehlerDifferential_lift_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_lift_comp
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [AddCommGroup M]
  [Module R M]
  [Module S M]
  [IsScalarTower R S M]
  {D' : Derivation R S M} :
-- imply
  D'.liftKaehlerDifferential.compDer (KaehlerDifferential.D R S) = D' :=
-- proof
  D'.liftKaehlerDifferential_comp

/--
[kaehlerDifferential_lift_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_lift_unique
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [AddCommGroup M]
  [Module R M]
  [Module S M]
  [IsScalarTower R S M]
  {f g : Ω[S⁄R] →ₗ[S] M}
-- given
  (hf : f.compDer (KaehlerDifferential.D R S) = g.compDer (KaehlerDifferential.D R S)) :
-- imply
  f = g :=
-- proof
  Derivation.liftKaehlerDifferential_unique f g hf

/--
[kaehlerDifferential_span_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_span_range
  {R : Type u}
  {S : Type v}
  [CommRing R]
  [CommRing S]
  [Algebra R S] :
-- imply
  Submodule.span S (Set.range (KaehlerDifferential.D R S)) = ⊤ :=
-- proof
  KaehlerDifferential.span_range_derivation R S
section PolynomialDifferentials
variable (k : Type u) [CommRing k]

/--
[kaehlerDifferential_polynomial_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_polynomial_free
  {k : Type u}
  [CommRing k] :
-- imply
  Module.Free (Polynomial k) (Ω[Polynomial k⁄k]) :=
-- proof
  Module.Free.of_equiv (KaehlerDifferential.polynomialEquiv k).symm

/--
[kaehlerDifferential_polynomial_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_polynomial_rank
  {k : Type u}
  [CommRing k]
  [Nontrivial k] :
-- imply
  Module.finrank (Polynomial k) (Ω[Polynomial k⁄k]) = 1 := by
-- proof
  have := (KaehlerDifferential.polynomialEquiv k).finrank_eq
  rw [this, Module.finrank_self]

/--
[kaehlerDifferential_polynomial_D](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_polynomial_D
  {k : Type u}
  [CommRing k]
  {P : Polynomial k} :
-- imply
  KaehlerDifferential.D k (Polynomial k) P = Polynomial.derivative P • KaehlerDifferential.D k (Polynomial k) Polynomial.X :=
-- proof
  KaehlerDifferential.polynomial_D_apply k P

/--
[kaehlerDifferential_mvPolynomial_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma kaehlerDifferential_mvPolynomial_free
  {k : Type u}
  [CommRing k]
  {σ : Type*} :
-- imply
  Module.Free (MvPolynomial σ k) (Ω[MvPolynomial σ k⁄k]) :=
-- proof
  inferInstance

/--
[cotangentSequence_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSequence_exact
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B] :
-- imply
  Function.Exact (KaehlerDifferential.mapBaseChange R A B) (KaehlerDifferential.map R A B B) :=
-- proof
  KaehlerDifferential.exact_mapBaseChange_map R A B

/--
[cotangentSequence_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSequence_surjective
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B] :
-- imply
  Function.Surjective (KaehlerDifferential.map R A B B) :=
-- proof
  KaehlerDifferential.map_surjective R A B

/--
[cotangentExactSequence_with_kernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentExactSequence_with_kernel
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) :=
-- proof
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

/--
[cotangent_mapBaseChange_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangent_mapBaseChange_surjective
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
-- proof
  KaehlerDifferential.mapBaseChange_surjective R A B h

/--
[proposition33_cotangent_exact_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma proposition33_cotangent_exact_sequence
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) ∧ Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
-- proof
  ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩

/--
[proposition33_part2_short_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma proposition33_part2_short_exact
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
  [Algebra.FormallySmooth R A]
  [Algebra.FormallySmooth R B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Injective (KaehlerDifferential.kerCotangentToTensor R A B) ∧ Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) ∧ Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
-- proof
  refine ⟨?_, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩
  rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff h]
  infer_instance
/-- Numerical consequence of Proposition 33: the rank of the conormal module `I/I²`
equals the difference between the ranks of `B ⊗_A Ω[A⁄R]` and `Ω[B⁄R]`. -/
section CotangentSpace

/--
[cotangent_finite_over_R](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangent_finite_over_R
  [CommRing R]
  [IsNoetherianRing R]
  {I : Ideal R} :
-- imply
  Module.Finite R I.Cotangent :=
-- proof
  Module.Finite.quotient _ _

/--
[cotangentSpace_finiteDimensional](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSpace_finiteDimensional
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  FiniteDimensional (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
-- proof
  inferInstance

/--
[cotangentSpace_zero_iff_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSpace_zero_iff_field
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  Subsingleton (IsLocalRing.CotangentSpace R) ↔ IsField R :=
-- proof
  IsLocalRing.subsingleton_cotangentSpace_iff

/--
[finrank_cotangentSpace_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma finrank_cotangentSpace_eq_zero_iff
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 0 ↔ IsField R :=
-- proof
  IsLocalRing.finrank_cotangentSpace_eq_zero_iff

/--
[cotangentSpace_dim_le_one_iff_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSpace_dim_le_one_iff_principal
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤ 1 ↔ (IsLocalRing.maximalIdeal R).IsPrincipal :=
-- proof
  IsLocalRing.finrank_cotangentSpace_le_one_iff
end CotangentSpace
section Smoothness

/--
[cotangentSpace_generators_iff_ideal_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSpace_generators_iff_ideal_generators
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
  {s : Set (IsLocalRing.maximalIdeal R)} :
-- imply
  Submodule.span (IsLocalRing.ResidueField R) ((IsLocalRing.maximalIdeal R).toCotangent '' s) = ⊤ ↔ Submodule.span R s = ⊤ :=
-- proof
  IsLocalRing.CotangentSpace.span_image_eq_top_iff

/--
[cotangentSpace_map_eq_top_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/KahlerDifferentials.lean)
-/
@[path]
lemma cotangentSpace_map_eq_top_iff
  {R : Type*}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R]
  {M : Submodule R (IsLocalRing.maximalIdeal R)} :
-- imply
  M.map (IsLocalRing.maximalIdeal R).toCotangent = ⊤ ↔ M = ⊤ :=
-- proof
  IsLocalRing.CotangentSpace.map_eq_top_iff
end Smoothness
end


-- created on 2026-10-23
