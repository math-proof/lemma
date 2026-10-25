import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RegularLocalRing
open KaehlerDifferential Algebra IsLocalRing


/--
[isRegularLocal_iff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma isRegularLocal_iff_eq
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  IsRegularLocal R ↔ ringKrullDim R = ↑(embDim R) :=
-- proof
  Iff.rfl

/--
[isRegularLocal_iff_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma isRegularLocal_iff_le
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  IsRegularLocal R ↔ (↑(embDim R) ≤ ringKrullDim R) := by
-- proof
  constructor
  · intro h
    exact le_of_eq h.symm
  · intro h
    exact le_antisymm (krullDim_le_embDim R) h

/--
[prop30_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma prop30_inequality
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  ringKrullDim R ≤ ↑(embDim R) :=
-- proof
  krullDim_le_embDim R

/--
[isRegularLocal_iff_embDim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma isRegularLocal_iff_embDim_eq
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  IsRegularLocal R ↔ ↑(embDim R) = ringKrullDim R := by
-- proof
  rw [isRegularLocal_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩
section CotangentSpaceConnection
variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/--
[cotangentSpace_finiteDimensional_regular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma cotangentSpace_finiteDimensional_regular
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  FiniteDimensional (ResidueField R) (CotangentSpace R) :=
-- proof
  inferInstance

/--
[cotangentSpace_subsingleton_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma cotangentSpace_subsingleton_iff
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  Subsingleton (CotangentSpace R) ↔ IsField R :=
-- proof
  subsingleton_cotangentSpace_iff

/--
[cotangentSpace_finrank_le_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma cotangentSpace_finrank_le_one_iff
  {R : Type u}
  [CommRing R]
  [IsLocalRing R]
  [IsNoetherianRing R] :
-- imply
  Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 ↔ (maximalIdeal R).IsPrincipal :=
-- proof
  finrank_cotangentSpace_le_one_iff
end CotangentSpaceConnection
section SmoothnessRegularity
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/--
[smooth_at_implies_exists_smooth_localization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma smooth_at_implies_exists_smooth_localization
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [FinitePresentation R A]
  {p : Ideal A}
  [p.IsPrime]
  [IsSmoothAt R p] :
-- imply
  ∃ f ∉ p, Smooth R (Localization.Away f) :=
-- proof
  exists_localization_smooth_of_smooth_at p

/--
[smooth_locus_regularity_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma smooth_locus_regularity_criterion
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [EssFiniteType R A] :
-- imply
  smoothLocus R A = (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R] :=
-- proof
  smoothLocus_eq_kahler_free_locus

/--
[smooth_iff_all_local_rings_in_smooth_locus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma smooth_iff_all_local_rings_in_smooth_locus
  {R : Type u}
  {A : Type v}
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [FinitePresentation R A] :
-- imply
  smoothLocus R A = Set.univ ↔ FormallySmooth R A :=
-- proof
  smooth_iff_smoothLocus_univ
end SmoothnessRegularity
section Examples
variable (k : Type u) [Field k]

/--
[field_isRegular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma field_isRegular
  {k : Type u}
  [Field k]
-- given
  (hk : IsField k) :
-- imply
  IsRegularLocal k :=
-- proof
  isRegularLocal_of_field k hk

/--
[DVR_isRegular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma DVR_isRegular
  {k : Type u}
  [Field k]
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R] :
-- imply
  IsRegularLocal R :=
-- proof
  isRegularLocal_of_DVR R

/--
[polynomial_ring_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma polynomial_ring_dim
  {k : Type u}
  [Field k]
  {n : ℕ} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k) = ↑n :=
-- proof
  smooth_ringKrullDim_mvPolynomial k n

/--
[prop30_for_polynomial_localization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RegularLocalRing.lean)
-/
@[path]
lemma prop30_for_polynomial_localization
  {k : Type u}
  [Field k]
  {n : ℕ}
  {𝔭 : Ideal (MvPolynomial (Fin n) k)}
  [𝔭.IsPrime] :
-- imply
  ringKrullDim (Localization.AtPrime 𝔭) ≤ ↑(embDim (Localization.AtPrime 𝔭)) :=
-- proof
  localization_mvPoly_krullDim_le_embDim k n 𝔭
end Examples


-- created on 2026-10-23
