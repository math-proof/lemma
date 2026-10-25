import Mathlib
import Instance.M4aHerbrand_SIdeleClassGroup
import Instance.NumberField_PlaceDecompositionAction
import Def.ExtCitation_LocalLevel_FundamentalClass

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

namespace NumberField.IdeleLocalInv

def HasLocalInv (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (_hactI : ∀ (g : K ≃ₐ[E] K) (y : (AdeleRing (𝓞 K) K)ˣ), g • y = D.unitsAct g y)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2)
    (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ)) : Prop :=
  ∃
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))

    (w : HeightOneSpectrum (𝓞 K)) (_ : w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal)

    (q : ℕ) (_ : Fact q.Prime) (_ : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
    (_ : MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E K w)) L') (_ : FaithfulSMul (↥(NumberField.PlaceDecomp.decomp E K w)) L')
    (_ : MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ)
    (Φ : w.adicCompletion K ≃+* L')
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : ℚ_[q]), g • algebraMap ℚ_[q] L' y = algebraMap ℚ_[q] L' y)
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : (↥L')ˣ), ((g • y : (↥L')ˣ) : L') = g • (y : L'))
    (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E K w)) (y : w.adicCompletion K), Φ (g • y) = g • Φ y)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] K₀)
    (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀)
    (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ ⟶
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (_ : ∀ y : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul y)) : (w.adicCompletion K)ˣ) : w.adicCompletion K) = Φ.symm (y : L'))

    (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (↥L')ˣ))
    (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E K w)) K₀ u')
    (n : ℤ),
    (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom x =
        n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E K w)) θ 2).hom u' ∧
      t = (((n : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp E K w) : ℚ) : ℚ) : AddCircle (1 : ℚ))

end NumberField.IdeleLocalInv
