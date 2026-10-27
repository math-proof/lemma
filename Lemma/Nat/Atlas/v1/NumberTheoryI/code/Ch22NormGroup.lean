import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
open Classical RayClassField
open scoped NumberField


namespace RayClassField

/--
[fracRelNorm_coeIdeal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
lemma fracRelNorm_coeIdeal_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {J : Ideal (𝓞 L)} :
-- imply
  fracRelNorm K L (↑J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = (↑(Ideal.relNorm (𝓞 K) J) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
-- proof
  show ↑(Ideal.relNorm (𝓞 K) (↑J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L).num) *
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
      ((algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L)
        (↑J : FractionalIdeal (nonZeroDivisors (𝓞 L)) L).den))⁻¹ =
    ↑(Ideal.relNorm (𝓞 K) J)
  set I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L := ↑J
  have hnum : I.num = Ideal.span {(I.den : 𝓞 L)} * J := by
    apply FractionalIdeal.coeIdeal_injective (K := L)
    push_cast [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
    exact (FractionalIdeal.den_mul_self_eq_num' (nonZeroDivisors (𝓞 L)) L I).symm
  rw [hnum, map_mul, Ideal.relNorm_singleton,
    FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  have hx : (algebraMap (𝓞 K) K) (Algebra.intNorm (𝓞 K) (𝓞 L) (I.den : 𝓞 L)) ≠ 0 :=
    algMap_intNorm_den_ne_zero K L I
  set a := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
    ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) (I.den : 𝓞 L)))
  set b := (↑(Ideal.relNorm (𝓞 K) J) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  set c := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
    ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) (I.den : 𝓞 L)))⁻¹
  have hac : a * c = 1 := by
    simp only [a, c, FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ hx, FractionalIdeal.spanSingleton_one]
  rw [mul_assoc, mul_comm b c, ← mul_assoc, hac, one_mul]

end RayClassField

namespace RayClassField

/--
[fracIdealNorm_prime_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
lemma fracIdealNorm_prime_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 L)} :
-- imply
  fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮) = (primeAsUnitFracIdeal K (lyingUnder K L 𝔮)) ^ (inertiaDegree' K L 𝔮) := by
-- proof
  apply Units.val_injective
  simp only [Units.val_pow_eq_pow_val, primeAsUnitFracIdeal_val,
    show (fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮)).val =
      fracRelNorm K L (primeAsUnitFracIdeal L 𝔮).val from rfl]
  rw [fracRelNorm_coeIdeal_eq]
  have hlo : 𝔮.asIdeal.LiesOver (lyingUnder K L 𝔮).asIdeal := by
    rw [Ideal.liesOver_iff, lyingUnder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  haveI := hlo
  haveI : (𝔮.asIdeal).IsMaximal := 𝔮.isMaximal
  haveI : (lyingUnder K L 𝔮).asIdeal.IsMaximal := (lyingUnder K L 𝔮).isMaximal
  rw [Ideal.relNorm_eq_pow_of_isMaximal 𝔮.asIdeal (lyingUnder K L 𝔮).asIdeal]
  simp only [FractionalIdeal.coeIdeal_pow, inertiaDegree']

end RayClassField

namespace RayClassField

/--
[idealNormMap_range_le_normGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
lemma idealNormMap_range_le_normGroup
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {𝔪 : Modulus K} :
-- imply
  (idealNormMap K L 𝔪).range ≤ NormGroup K L 𝔪 :=
-- proof
  le_sup_right

end RayClassField

/--
[fiber_under_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma fiber_under_finite_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} :
-- imply
  Set.Finite {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) | IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝔮 = 𝔭} := by
-- proof
  apply RayClassField.fiber_under_finite K L 𝔭

/--
[extendModulus_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma extendModulus_finite_support_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {𝔪 : Modulus K} :
-- imply
  Set.Finite {v : Place L | (match v with | Place.finite 𝔮 => ramificationIndex' K L 𝔮 * 𝔪.toFun (Place.finite (lyingUnder K L 𝔮)) | Place.infinite w => if w.IsComplex then 0 else 𝔪.toFun (Place.infinite (w.comap (algebraMap K L)))) ≠ 0} := by
-- proof
  apply RayClassField.extendModulus_finite_support K L 𝔪

/--
[cgwz_rearrange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma cgwz_rearrange_eq
  [CommGroupWithZero α]
  {a b c d e f : α}
-- given
  (ha : a ≠ 0)
  (hd : d ≠ 0)
  (he : e ≠ 0)
  (h : a * b * c = d * e * f) :
-- imply
  f * a⁻¹ = b * d⁻¹ * (c * e⁻¹) := by
-- proof
  apply RayClassField.cgwz_rearrange ha hd he h

/--
[algMap_intNorm_den_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma algMap_intNorm_den_ne_zero_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L} :
-- imply
  (algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑I.den) ≠ 0 := by
-- proof
  apply RayClassField.algMap_intNorm_den_ne_zero K L I

/--
[spanSingleton_intNorm_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma spanSingleton_intNorm_ne_zero_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [NumberField K]
  [Field L]
  [NumberField L]
  [Algebra K L]
  {I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L} :
-- imply
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) ((algebraMap (𝓞 K) K) ((Algebra.intNorm (𝓞 K) (𝓞 L)) ↑I.den)) ≠ 0 := by
-- proof
  apply RayClassField.spanSingleton_intNorm_ne_zero K L I

/--
[ramificationIndex'_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma ramificationIndex'_pos_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)} :
-- imply
  0 < ramificationIndex' K L 𝔮 := by
-- proof
  apply RayClassField.ramificationIndex'_pos K L 𝔮

/--
[norm_trivialValuation_of_all_lying_over](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma norm_trivialValuation_of_all_lying_over_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {x : L}
  {v : FinitePlace K}
-- given
  (hx : x ≠ 0)
  (hw : ∀ w : FinitePlace L, lyingUnder K L w = v → IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1) :
-- imply
  IsDedekindDomain.HeightOneSpectrum.valuation K v (Algebra.norm K x) = 1 := by
-- proof
  apply RayClassField.norm_trivialValuation_of_all_lying_over K L x v hx hw

/--
[fracIdeal_exists_simultaneous_trivialValuation_finset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma fracIdeal_exists_simultaneous_trivialValuation_finset_eq
  {L : Type u}
  [Field L]
  [NumberField L]
  {I : (FracIdeal L)ˣ}
  {S : Finset (FinitePlace L)}
-- given
  (hI : ∀ w ∈ S, HasTrivialValuation I w) :
-- imply
  ∃ x ∈ (I : FracIdeal L), x ≠ 0 ∧ ∀ w ∈ S, IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1 := by
-- proof
  apply RayClassField.fracIdeal_exists_simultaneous_trivialValuation_finset I S hI

/--
[exists_simultaneous_trivialValuation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma exists_simultaneous_trivialValuation_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {I : (FracIdeal L)ˣ}
  {v : FinitePlace K}
-- given
  (hI : ∀ w : FinitePlace L, lyingUnder K L w = v → HasTrivialValuation I w) :
-- imply
  ∃ x ∈ (I : FracIdeal L), x ≠ 0 ∧ ∀ w : FinitePlace L, lyingUnder K L w = v → IsDedekindDomain.HeightOneSpectrum.valuation L w x = 1 := by
-- proof
  apply RayClassField.exists_simultaneous_trivialValuation K L I v hI

/--
[norm_mem_fracRelNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma norm_mem_fracRelNorm_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {I : FracIdeal L}
  {x : L}
-- given
  (hx : x ∈ I) :
-- imply
  Algebra.norm K x ∈ (fracRelNorm K L I : FracIdeal K) := by
-- proof
  apply RayClassField.norm_mem_fracRelNorm K L I x hx

/--
[hasTrivialValuation_fracIdealNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma hasTrivialValuation_fracIdealNorm_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {I : (FracIdeal L)ˣ}
  {v : FinitePlace K}
-- given
  (hI : ∀ w : FinitePlace L, lyingUnder K L w = v → HasTrivialValuation I w) :
-- imply
  HasTrivialValuation (fracIdealNorm K L I) v := by
-- proof
  apply RayClassField.hasTrivialValuation_fracIdealNorm K L I v hI

/--
[fracIdealNorm_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma fracIdealNorm_coprime_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {𝔪 : Modulus K}
  {I : (FracIdeal L)ˣ}
-- given
  (hI : I ∈ FracIdealsCoprime_subgroup L (extendModulus K L 𝔪)) :
-- imply
  fracIdealNorm K L I ∈ FracIdealsCoprime_subgroup K 𝔪 := by
-- proof
  apply RayClassField.fracIdealNorm_coprime K L 𝔪 I hI

/--
[rayGroup_le_normGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22NormGroup.lean)
-/
@[path]
private lemma rayGroup_le_normGroup_eq
  {K : Type u}
  {L : Type u}
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [IsGalois K L]
  {𝔪 : Modulus K} :
-- imply
  RayGroup K 𝔪 ≤ NormGroup K L 𝔪 := by
-- proof
  apply RayClassField.rayGroup_le_normGroup K L 𝔪


-- created on 2026-10-23
