import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz.Part2
open MvPolynomial AlgebraicGeometry CategoryTheory Lec1ZariskiNullstellensatz


namespace Lec1ZariskiNullstellensatz

/--
[thm1_1_essential_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma thm1_1_essential_nullstellensatz
  {k K : Type*}
  [Field k]
  [Field K]
  [Algebra k K]
  [Algebra.FiniteType k K] :
-- imply
  Algebra.IsAlgebraic k K := by
-- proof
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  exact Algebra.IsAlgebraic.of_finite k K

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[thm1_1_essential_nullstellensatz_algClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma thm1_1_essential_nullstellensatz_algClosed
  {k K : Type*}
  [Field k]
  [IsAlgClosed k]
  [Field K]
  [Algebra k K]
  [Algebra.FiniteType k K] :
-- imply
  Function.Bijective (algebraMap k K) := by
-- proof
  have : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  have : Algebra.IsIntegral k K := Algebra.IsAlgebraic.isIntegral
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[isZariskiClosed_iff_exists_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma isZariskiClosed_iff_exists_ideal
  {k : Type*}
  [Field k]
  {σ : Type*}
  {V : Set (σ → k)} :
-- imply
  IsZariskiClosed k σ V ↔ ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I := by
-- proof
  constructor
  · rintro ⟨S, rfl⟩
    exact ⟨Ideal.span S, (MvPolynomial.zeroLocus_span S).symm⟩
  · rintro ⟨I, rfl⟩
    exact ⟨I, rfl⟩

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[nullstellensatz_correspondence_eq_radical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma nullstellensatz_correspondence_eq_radical
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {σ : Type*}
  [Finite σ]
  {I : Ideal (MvPolynomial σ k)} :
-- imply
  MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I.radical :=
-- proof
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[nullstellensatz_radical_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma nullstellensatz_radical_inverse
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {σ : Type*}
  [Finite σ]
  {I : Ideal (MvPolynomial σ k)}
-- given
  (hI : I.IsRadical) :
-- imply
  MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I) = I := by
-- proof
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hI.radical]

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[nullstellensatz_closed_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma nullstellensatz_closed_inverse
  {k : Type*}
  [Field k]
  [IsAlgClosed k]
  {σ : Type*}
  [Finite σ]
  {I : Ideal (MvPolynomial σ k)} :
-- imply
  MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus k I)) = MvPolynomial.zeroLocus k I := by
-- proof
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := k) I, zeroLocus_radical_eq]

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[zariskiTopology_isClosed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma zariskiTopology_isClosed_iff
  {k : Type*}
  [Field k]
  {σ : Type*}
  [Fintype σ]
  {Z : Set (σ → k)} :
-- imply
  @IsClosed _ (zariskiTopology_classical k σ) Z ↔ IsZariskiClosed k σ Z := by
-- proof
  constructor
  · intro hZ
    have hopen := hZ.isOpen_compl
    change Zᶜᶜ ∈ {V | ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I} at hopen
    rw [compl_compl] at hopen
    obtain ⟨I, rfl⟩ := hopen
    exact ⟨I, rfl⟩
  · intro ⟨S, hS⟩
    constructor
    show Zᶜᶜ ∈ {V | ∃ I : Ideal (MvPolynomial σ k), V = MvPolynomial.zeroLocus k I}
    rw [compl_compl]
    exact ⟨Ideal.span S, by rw [hS, MvPolynomial.zeroLocus_span]⟩

end Lec1ZariskiNullstellensatz

namespace Lec1ZariskiNullstellensatz

/--
[isAffineVariety_of_finiteType](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
lemma isAffineVariety_of_finiteType
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
-- given
  (hfin : Algebra.FiniteType k A) :
-- imply
  IsAffineVariety' k A where finiteType :=
-- proof
  hfin
    yoneda_bijective := fun X => Equiv.bijective (affine_variety_yoneda (CommRingCat.of A) X)

end Lec1ZariskiNullstellensatz

/--
[vanishingIdeal_isRadical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
private lemma vanishingIdeal_isRadical_eq
  {k : Type*}
  [Field k]
  {σ : Type*}
  {V : Set (σ → k)} :
-- imply
  (MvPolynomial.vanishingIdeal k V).IsRadical := by
-- proof
  apply Lec1ZariskiNullstellensatz.vanishingIdeal_isRadical k σ V

/--
[zeroLocus_radical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean)
-/
@[path]
private lemma zeroLocus_radical_eq_eq
  {k : Type*}
  [Field k]
  {σ : Type*}
  {I : Ideal (MvPolynomial σ k)} :
-- imply
  MvPolynomial.zeroLocus k I.radical = MvPolynomial.zeroLocus k I := by
-- proof
  apply Lec1ZariskiNullstellensatz.zeroLocus_radical_eq k σ I


-- created on 2026-10-23
