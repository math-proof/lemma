import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent.Part3
open KaehlerDifferential Module


/--
[prop35a_smooth_kahler_projective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop35a_smooth_kahler_projective
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  [Algebra.FormallySmooth R A] :
-- imply
  Module.Projective A (Ω[A⁄R]) :=
-- proof
  Algebra.FormallySmooth.projective_kaehlerDifferential

/--
[prop35b_conormal_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop35b_conormal_exact
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  {B : Type w}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B]
-- given
  (hAB : Function.Surjective (algebraMap A B)) :
-- imply
  LinearMap.range (kerCotangentToTensor R A B) = (LinearMap.ker (mapBaseChange R A B)).restrictScalars A :=
-- proof
  range_kerCotangentToTensor R A B hAB

/--
[prop35b_conormal_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop35b_conormal_surjective
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  {B : Type w}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B] :
-- imply
  Function.Surjective (KaehlerDifferential.map R A B B) :=
-- proof
  KaehlerDifferential.map_surjective R A B

/--
[prop35b_jacobi_zariski_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop35b_jacobi_zariski_exact
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  {B : Type w}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B] :
-- imply
  Function.Exact (mapBaseChange R A B) (KaehlerDifferential.map R A B B) :=
-- proof
  exact_mapBaseChange_map R A B

/--
[prop35c_smooth_conormal_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop35c_smooth_conormal_injective
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  [Algebra.FormallySmooth R A]
  {P : Algebra.Extension R A}
  [Algebra.FormallySmooth R P.Ring] :
-- imply
  Function.Injective P.cotangentComplex := by
-- proof
  rwa [P.cotangentComplex_injective_iff]
section Corollary25
variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]

/--
[cor25_smooth_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma cor25_smooth_criterion
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  {B : Type w}
  [CommRing B]
  [Algebra R B] :
-- imply
  Algebra.FormallySmooth R B ↔ (Module.Projective B (Ω[B⁄R]) ∧ Subsingleton (Algebra.H1Cotangent R B)) :=
-- proof
  Algebra.formallySmooth_iff R B

/--
[cor25_conormal_injective_iff_h1_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma cor25_conormal_injective_iff_h1_vanishes
  {R : Type u}
  [CommRing R]
  {A : Type v}
  [CommRing A]
  [Algebra R A]
  [Algebra.FormallySmooth R A]
  {B : Type w}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B]
-- given
  (hAB : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Injective (kerCotangentToTensor R A B) ↔ Subsingleton (Algebra.H1Cotangent R B) :=
-- proof
  Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hAB
end Corollary25
section EulerSequence
variable (k : Type u) [Field k] (n : ℕ)

/--
[euler_seq_kahler_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma euler_seq_kahler_rank
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) = n + 1 := by
-- proof
  rw [Module.finrank_eq_card_basis (euler_seq_kahler_basis k n), Fintype.card_fin]

/--
[euler_seq_canonical_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma euler_seq_canonical_rank
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  Module.finrank (PolyRingLec20 k n) (⋀[PolyRingLec20 k n]^(n + 1) (Ω[PolyRingLec20 k n⁄k])) = 1 := by
-- proof
  rw [exteriorPower.finrank_eq]
  rw [Module.finrank_eq_card_basis (euler_seq_kahler_basis k n)]
  simp [Fintype.card_fin, Nat.choose_self]
end EulerSequence
section TautologicalBundle
variable (F : Type u) [Field F]
variable (W : Type v) [AddCommGroup W] [Module F W]

/--
[tautologicalSubspace_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma tautologicalSubspace_eq
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  tautologicalSubspace F W kk V = V.toSubmodule :=
-- proof
  rfl

/--
[tautological_rank_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma tautological_rank_constant
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  ∀ p, rankAtStalk (R := F) (W ⧸ V.toSubmodule) p = kk :=
-- proof
  V.rankAtStalk_eq

/--
[grassmannian_quotient_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma grassmannian_quotient_finrank
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  Module.finrank F (W ⧸ V.toSubmodule) = kk := by
-- proof
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  have h1 := Module.rankAtStalk_eq_finrank_of_free (R := F) (M := W ⧸ V.toSubmodule)
  have h2 := V.rankAtStalk_eq (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  rw [h1] at h2
  exact Nat.cast_injective h2

/--
[grassmannian_submodule_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma grassmannian_submodule_finrank
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk} :
-- imply
  Module.finrank F (↥V.toSubmodule) = Module.finrank F W - kk := by
-- proof
  have hQ := grassmannian_quotient_finrank F W kk V
  have := Submodule.finrank_quotient_add_finrank V.toSubmodule
  omega
end TautologicalBundle
section Proposition37
variable (F : Type u) [Field F]
variable (W : Type v) [AddCommGroup W] [Module F W]

/--
[prop37_grassmannian_tangent_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop37_grassmannian_tangent_dim
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk}
  [FiniteDimensional F V.toSubmodule]
  [FiniteDimensional F (W ⧸ V.toSubmodule)] :
-- imply
  Module.finrank F (grassmannianTangentSpace F W kk V) = Module.finrank F (↥V.toSubmodule) * Module.finrank F (W ⧸ V.toSubmodule) := by
-- proof
  change Module.finrank F (↥V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)) = _
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  exact Module.finrank_linearMap F F (↥V.toSubmodule) (W ⧸ V.toSubmodule)

/--
[prop37_grassmannian_cotangent_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop37_grassmannian_cotangent_dim
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk}
  [FiniteDimensional F V.toSubmodule]
  [FiniteDimensional F (W ⧸ V.toSubmodule)] :
-- imply
  Module.finrank F (grassmannianCotangentSpace F W kk V) = Module.finrank F (W ⧸ V.toSubmodule) * Module.finrank F (↥V.toSubmodule) := by
-- proof
  change Module.finrank F ((W ⧸ V.toSubmodule) →ₗ[F] ↥V.toSubmodule) = _
  haveI : Module.Free F (↥V.toSubmodule) := Module.Free.of_divisionRing F _
  haveI : Module.Free F (W ⧸ V.toSubmodule) := Module.Free.of_divisionRing F _
  exact Module.finrank_linearMap F F (W ⧸ V.toSubmodule) (↥V.toSubmodule)

/--
[prop37_tangent_eq_cotangent_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop37_tangent_eq_cotangent_dim
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {kk : ℕ}
  {V : Module.Grassmannian F W kk}
  [FiniteDimensional F V.toSubmodule]
  [FiniteDimensional F (W ⧸ V.toSubmodule)] :
-- imply
  Module.finrank F (grassmannianTangentSpace F W kk V) = Module.finrank F (grassmannianCotangentSpace F W kk V) := by
-- proof
  rw [prop37_grassmannian_tangent_dim, prop37_grassmannian_cotangent_dim]
  ring

/--
[prop37_euler_specialization_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop37_euler_specialization_dim
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  [FiniteDimensional F W]
  {V : Module.Grassmannian F W 1}
  [FiniteDimensional F V.toSubmodule]
  [FiniteDimensional F (W ⧸ V.toSubmodule)] :
-- imply
  Module.finrank F (grassmannianTangentSpace F W 1 V) = Module.finrank F (↥V.toSubmodule) * Module.finrank F (W ⧸ V.toSubmodule) :=
-- proof
  prop37_grassmannian_tangent_dim F W 1 V

/--
[prop37_projective_space_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean)
-/
@[path]
lemma prop37_projective_space_dim
  {F : Type u}
  [Field F]
  {W : Type v}
  [AddCommGroup W]
  [Module F W]
  {n : ℕ}
  [FiniteDimensional F W]
  {V : Module.Grassmannian F W 1}
-- given
  (hW : Module.finrank F W = n + 1) :
-- imply
  Module.finrank F (grassmannianTangentSpace F W 1 V) = n := by
-- proof
  haveI : FiniteDimensional F (W ⧸ V.toSubmodule) := V.finite_quotient
  haveI : FiniteDimensional F V.toSubmodule :=
    Submodule.finiteDimensional_of_le le_top
  rw [prop37_grassmannian_tangent_dim]
  have hQ : Module.finrank F (W ⧸ V.toSubmodule) = 1 :=
    grassmannian_quotient_finrank F W 1 V
  have hV : Module.finrank F (↥V.toSubmodule) = n := by
    have := grassmannian_submodule_finrank F W 1 V
    omega
  rw [hV, hQ]
  ring
end Proposition37


-- created on 2026-10-23
