import Mathlib
import Def.FLTPrelim_Ramification
import Lemma.EllipticCurve.FrobeniusTrace
import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.Correspondence
import Def.AlgebraicCurve_WeilDatum
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.ModularCurve.QExpReductionModL
import Structure.ModularCurve_QExpSemistableSpecializationPinned

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField

namespace ModularCurve

namespace QExpSemistable

section Vocabulary

variable {K : Type*} [Field K]


theorem IsQExpInclusion.injective {E E' : IntermediateField K (LaurentSeries K)} {ι : E →ₐ[K] E'}
    (h : IsQExpInclusion ι) : Function.Injective ι := fun x y hxy =>
  Subtype.ext (by rw [← h x, ← h y, hxy])

theorem isQExpInclusion_inclusion {E E' : IntermediateField K (LaurentSeries K)} (hle : E ≤ E') :
    IsQExpInclusion (E := E) (E' := E') (IntermediateField.inclusion hle) := fun x =>
  IntermediateField.coe_inclusion hle x

variable {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']


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
