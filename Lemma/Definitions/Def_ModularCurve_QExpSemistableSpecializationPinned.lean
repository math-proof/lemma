import Mathlib
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Definitions.Def_AlgebraicCurve_WeilDatum
import Lemma.Definitions.Def_ModularCurve_ArithmeticGalois
import Lemma.Definitions.Def_ModularCurve_QExpReductionModL

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField

namespace ModularCurve

namespace QExpSemistable

section Vocabulary

variable {K : Type*} [Field K]

def IsQExpInclusion {E E' : IntermediateField K (LaurentSeries K)} (ι : E →ₐ[K] E') : Prop :=
  ∀ x : E, ((ι x : E') : LaurentSeries K) = (x : LaurentSeries K)

theorem IsQExpInclusion.injective {E E' : IntermediateField K (LaurentSeries K)} {ι : E →ₐ[K] E'}
    (h : IsQExpInclusion ι) : Function.Injective ι := fun x y hxy =>
  Subtype.ext (by rw [← h x, ← h y, hxy])

theorem isQExpInclusion_inclusion {E E' : IntermediateField K (LaurentSeries K)} (hle : E ≤ E') :
    IsQExpInclusion (E := E) (E' := E') (IntermediateField.inclusion hle) := fun x =>
  IntermediateField.coe_inclusion hle x

variable {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']

def IsConormAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (D₁ : Divisor K F)
    (D : Divisor K F') : Prop :=
  ∀ w : Place K F', D w = (Place.ramificationIndexAlong φ w : ℤ) * D₁ (Place.restrictAlong φ hφ w)

theorem IsConormAlong.zero (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) :
    IsConormAlong φ hφ 0 0 := fun _ => by
  rw [Finsupp.zero_apply, Finsupp.zero_apply, mul_zero]

theorem IsConormAlong.add {φ : F →ₐ[K] F'} {hφ : φ.toRingHom.IsIntegral} {D₁ E₁ : Divisor K F}
    {D E : Divisor K F'} (hD : IsConormAlong φ hφ D₁ D) (hE : IsConormAlong φ hφ E₁ E) :
    IsConormAlong φ hφ (D₁ + E₁) (D + E) := fun w => by
  rw [Finsupp.add_apply, Finsupp.add_apply, hD w, hE w, mul_add]

theorem IsConormAlong.neg {φ : F →ₐ[K] F'} {hφ : φ.toRingHom.IsIntegral} {D₁ : Divisor K F}
    {D : Divisor K F'} (hD : IsConormAlong φ hφ D₁ D) : IsConormAlong φ hφ (-D₁) (-D) := fun w => by
  rw [Finsupp.neg_apply, Finsupp.neg_apply, hD w, mul_neg]

theorem IsConormAlong.unique {φ : F →ₐ[K] F'} {hφ : φ.toRingHom.IsIntegral} {D₁ : Divisor K F}
    {D D' : Divisor K F'} (hD : IsConormAlong φ hφ D₁ D) (hD' : IsConormAlong φ hφ D₁ D') :
    D = D' :=
  Finsupp.ext fun w => (hD w).trans (hD' w).symm

end Vocabulary

end QExpSemistable

section Datum

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
variable (P : ValuationSubring (AlgebraicClosure ℚ))
variable (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (q : ℕ)
variable (k : Type) [Field k] (π : P →+* k)
variable (Fbar : IntermediateField k (LaurentSeries k))
variable (F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (Fbar₁ : IntermediateField k (LaurentSeries k))

set_option maxHeartbeats 1000000 in

structure QExpSemistableSpecializationPinned where

  nodes : Finset (Place k Fbar × Place k Fbar)

  nodes_rational : ∀ s ∈ nodes,
    Function.Surjective (algebraMap k s.1.ResidueField) ∧
      Function.Surjective (algebraMap k s.2.ResidueField)

  frob : SemilinearAut k Fbar

  coeff_frob_smul : ∀ (x : Fbar) (n : ℤ),
    ((frob • x : Fbar) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ q

  dom : AddSubgroup (Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀))

  smul_eq_self_of_mem_dom : ∀ y ∈ dom, ∀ σ ∈ I, σ • y = y

  exists_nsmul_mem_dom : ∃ m : ℕ, 0 < m ∧
    ∀ y : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀),
      (∀ σ ∈ I, σ • y = y) → m • y ∈ dom

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

namespace QExpSemistableSpecializationPinned

variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
variable {P : ValuationSubring (AlgebraicClosure ℚ)}
variable {I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {q : ℕ}
variable {k : Type} [Field k] {π : P →+* k}
variable {Fbar : IntermediateField k (LaurentSeries k)}
variable {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} {Fbar₁ : IntermediateField k (LaurentSeries k)}
variable (𝒟 : QExpSemistableSpecializationPinned F₀ P I q k π Fbar F₁ Fbar₁)

theorem baseAut_frob (a : k) : SemilinearAut.baseAut 𝒟.frob a = a ^ q := by
  have hcoe : ∀ b : k, ((algebraMap k Fbar b : Fbar) : LaurentSeries k).coeff 0 = b := fun b => by
    have e : ((algebraMap k Fbar b : Fbar) : LaurentSeries k) = algebraMap k (LaurentSeries k) b :=
      IntermediateField.coe_algebraMap_apply Fbar b
    rw [e, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_same]
  have h₁ := 𝒟.coeff_frob_smul (algebraMap k Fbar a) 0
  rw [SemilinearAut.smul_algebraMap, hcoe, hcoe] at h₁
  exact h₁

theorem frob_smul_eq {I' : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    {F₁' : IntermediateField ℚ (LaurentSeries ℚ)} {Fbar₁' : IntermediateField k (LaurentSeries k)}
    (𝒟' : QExpSemistableSpecializationPinned F₀ P I' q k π Fbar F₁' Fbar₁') (x : Fbar) :
    𝒟.frob • x = 𝒟'.frob • x := by
  refine Subtype.ext (HahnSeries.ext (funext fun n => ?_))
  rw [𝒟.coeff_frob_smul, 𝒟'.coeff_frob_smul]

def toricPart : AddSubgroup 𝒟.dom :=
  ((GluedPic0.toPic0Pair 𝒟.nodes).comp 𝒟.sp).ker

theorem mem_toricPart {y : 𝒟.dom} :
    y ∈ 𝒟.toricPart ↔ GluedPic0.toPic0Pair 𝒟.nodes (𝒟.sp y) = 0 :=
  Iff.rfl

theorem pairing_eq_one_of_toPic0Pair_sp_eq_zero_right {n : ℕ} (hn : 0 < n) (hqn : ¬ q ∣ n)
    (d : WeilDatum (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) n)
    (E₁ E₂ : Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hE₁ : (E₁ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = d.D₁)
    (hE₂ : (E₂ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = d.D₂)
    (h₁ : Pic0.mk E₁ ∈ 𝒟.dom) (h₂ : Pic0.mk E₂ ∈ 𝒟.dom)
    (htor : GluedPic0.toPic0Pair 𝒟.nodes (𝒟.sp ⟨Pic0.mk E₂, h₂⟩) = 0) : d.pairing = 1 := by
  have h := 𝒟.pairing_eq_one_of_toPic0Pair_sp_eq_zero n hn hqn d.symm E₂ E₁ hE₂ hE₁ h₂ h₁ htor
  have hd : d.symm.pairing = d.pairing⁻¹ := by
    show Divisor.evalFun d.f₂ d.D₁ / Divisor.evalFun d.f₁ d.D₂ =
      (Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁)⁻¹
    rw [inv_div]
  rw [hd] at h
  exact inv_eq_one.mp h

theorem pairing_eq_one_of_mem_toricPart {n : ℕ} (hn : 0 < n) (hqn : ¬ q ∣ n)
    (d : WeilDatum (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀) n)
    (E₁ E₂ : Divisor.degZero (K := AlgebraicClosure ℚ)
      (F := laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hE₁ : (E₁ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = d.D₁)
    (hE₂ : (E₂ : Divisor (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) F₀)) = d.D₂)
    (h₁ : Pic0.mk E₁ ∈ 𝒟.dom) (h₂ : Pic0.mk E₂ ∈ 𝒟.dom)
    (htor : (⟨Pic0.mk E₁, h₁⟩ : 𝒟.dom) ∈ 𝒟.toricPart ∨ (⟨Pic0.mk E₂, h₂⟩ : 𝒟.dom) ∈ 𝒟.toricPart) :
    d.pairing = 1 := by
  rcases htor with ht | ht
  · exact 𝒟.pairing_eq_one_of_toPic0Pair_sp_eq_zero n hn hqn d E₁ E₂ hE₁ hE₂ h₁ h₂ ht
  · exact 𝒟.pairing_eq_one_of_toPic0Pair_sp_eq_zero_right hn hqn d E₁ E₂ hE₁ hE₂ h₁ h₂ ht

end QExpSemistableSpecializationPinned

end ModularCurve

end
