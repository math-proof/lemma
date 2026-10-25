import Mathlib
import Def.FLTPrelim_Ramification
import Instance.EllipticCurve_FrobeniusTrace
import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.Correspondence
import Structure.AlgebraicCurve_WeilDatum
import Instance.ModularCurve_ArithmeticGalois
import Lemma.ModularCurve.QExpReductionModL
import Structure.ModularCurve_QExpSemistableSpecializationPinned

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField

namespace ModularCurve

section Datum

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
variable (P : ValuationSubring (AlgebraicClosure ℚ))
variable (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (q : ℕ)
variable (k : Type) [Field k] (π : P →+* k)
variable (Fbar : IntermediateField k (LaurentSeries k))
variable (F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (Fbar₁ : IntermediateField k (LaurentSeries k))

set_option maxHeartbeats 1000000 in

structure QExpSemistableSpecializationPinnedV3 where

  nodes : Finset (Place k Fbar × Place k Fbar)

  nodes_rational : ∀ s ∈ nodes,
    Function.Surjective (algebraMap k s.1.ResidueField) ∧
      Function.Surjective (algebraMap k s.2.ResidueField)

  frob : SemilinearAut k Fbar

  coeff_frob_smul : ∀ (x : Fbar) (n : ℤ),
    ((frob • x : Fbar) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ q

  dom : AddSubgroup (Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀))

  smul_eq_self_of_mem_dom : ∀ y ∈ dom, ∀ σ ∈ I, σ • y = y

  smul_mem_dom_of_isFrobeniusAt : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    P.IsFrobeniusAt φ q → (∀ σ, σ ∈ I ↔ φ * σ * φ⁻¹ ∈ I) → ∀ y ∈ dom, φ • y ∈ dom

  sp : dom →+ GluedPic0 k Fbar nodes

  sp_injective : ∀ y : dom,
    (∃ n : ℕ, 0 < n ∧ ¬ q ∣ n ∧
      n • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = 0) →
      sp y = 0 → y = 0

  sp_surjective : ∀ ξ : GluedPic0 k Fbar nodes, (∃ n : ℕ, 0 < n ∧ ¬ q ∣ n ∧ n • ξ = 0) →
    ∃ y : dom, (∃ n : ℕ, 0 < n ∧ ¬ q ∣ n ∧
      n • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = 0) ∧ sp y = ξ

  finite_torsion_and_natCard_eq : ∀ n : ℕ, 0 < n → ¬ q ∣ n →
    Finite (Pic0.torsion (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) n) ∧
      Nat.card (Pic0.torsion (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) n) =
        Nat.card {ξ : GluedPic0 k Fbar nodes // n • ξ = 0} *
          Nat.card {ξ : GluedPic0 k Fbar nodes // n • ξ = 0 ∧ GluedPic0.toPic0Pair nodes ξ = 0}

  toPic0Pair_sp_fst_smul_of_isFrobeniusAt : ∀ φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    P.IsFrobeniusAt φ q → ∀ (y : dom)
      (h : φ • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) ∈ dom),
      (GluedPic0.toPic0Pair nodes
          (sp ⟨φ • (y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)), h⟩)).1 =
        frob • (GluedPic0.toPic0Pair nodes (sp y)).1

  toPic0Pair_sp_fst_eq :
    ∀ (r₁ : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₁) → Place k Fbar₁),
      IsLaurentPlaceReduction P π F₁ Fbar₁ r₁ →
      LaurentPrincipalGeneratedByIntegral P π F₁ Fbar₁ →
      ∀ (ι : laurentBaseChange (AlgebraicClosure ℚ) F₁ →ₐ[AlgebraicClosure ℚ]
          laurentBaseChange (AlgebraicClosure ℚ) F₀)
        (hι : ι.toRingHom.IsIntegral) (ῑ : Fbar₁ →ₐ[k] Fbar) (hῑ : ῑ.toRingHom.IsIntegral),
        QExpSemistable.IsQExpInclusion ι → QExpSemistable.IsQExpInclusion ῑ →
        ∀ (D₁ : Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := laurentBaseChange (AlgebraicClosure ℚ) F₁))
          (D : Divisor.degZero (K := AlgebraicClosure ℚ)
            (F := laurentBaseChange (AlgebraicClosure ℚ) F₀)),
          QExpSemistable.IsConormAlong ι hι
            (D₁ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₁))
            (D : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) →
          ∀ (hD : Pic0.mk D ∈ dom) (Dbar : Divisor.degZero (K := k) (F := Fbar)),
            QExpSemistable.IsConormAlong ῑ hῑ
              (Finsupp.mapDomain r₁
                (D₁ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₁)))
              (Dbar : Divisor k Fbar) →
            (GluedPic0.toPic0Pair nodes (sp ⟨Pic0.mk D, hD⟩)).1 = Pic0.mk Dbar

  pairing_eq_one_of_toPic0Pair_sp_eq_zero : ∀ (n : ℕ), 0 < n → ¬ q ∣ n →
    ∀ (d : WeilDatum (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) n)
      (E₁ E₂ : Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := laurentBaseChange (AlgebraicClosure ℚ) F₀)),
      (E₁ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = d.D₁ →
      (E₂ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = d.D₂ →
      ∀ (h₁ : Pic0.mk E₁ ∈ dom), Pic0.mk E₂ ∈ dom →
        GluedPic0.toPic0Pair nodes (sp ⟨Pic0.mk E₁, h₁⟩) = 0 → d.pairing = 1

end Datum

namespace QExpSemistableSpecializationPinnedV3

variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
variable {P : ValuationSubring (AlgebraicClosure ℚ)}
variable {I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {q : ℕ}
variable {k : Type} [Field k] {π : P →+* k}
variable {Fbar : IntermediateField k (LaurentSeries k)}
variable {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} {Fbar₁ : IntermediateField k (LaurentSeries k)}
variable (𝒟 : QExpSemistableSpecializationPinnedV3 F₀ P I q k π Fbar F₁ Fbar₁)


end QExpSemistableSpecializationPinnedV3

end ModularCurve

end
