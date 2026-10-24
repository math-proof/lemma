import Lemma.Definitions.Def_ModularCurve_MazurStepThreeInputs
import Lemma.Definitions.Def_ModularCurve_HeckeModule

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve

namespace ModularCurve

local notation "Qbar" => AlgebraicClosure ℚ

variable {p : ℕ} [NeZero p] {T : Type*} [AddCommGroup T]

def TorsBijFor (ℓ : ℕ) (sp : JZero p →+ T) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ ℓ → ∀ y : T, (∃ n : ℕ, q ^ n • y = 0) →
    ∃ x : JZero p, (∃ n : ℕ, q ^ n • x = 0) ∧ sp x = y

def FTorsionFor (T : Type*) [AddCommGroup T] : Prop :=
  ∀ y : T, ∃ m : ℕ, 0 < m ∧ m • y = 0

def CuspRuleStrongFor (A : ValuationSubring Qbar) (sp : JZero p →+ T) : Prop :=
  ∀ (x : Place Qbar (modularFunctionFieldBar p)) (j₁ j₂ : Qbar)
      (hinf : placeDiff p x (cuspInftyBar p) ∈ Divisor.degZero)
      (hzero : placeDiff p x (cuspZeroBar p) ∈ Divisor.degZero),
    (∀ σ : Qbar ≃ₐ[ℚ] Qbar, arithmeticGalois (modularFunctionFieldFull p) σ • x = x) →
    0 < x.ord (jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁) →
    0 < x.ord (jpBar p - algebraMap Qbar (modularFunctionFieldBar p) j₂) →
    1 < A.valuation j₁ →
      (A.valuation j₂ = A.valuation j₁ ^ p →
        sp (Pic0.mk ⟨placeDiff p x (cuspInftyBar p), hinf⟩) = 0) ∧
      (A.valuation j₂ ^ p = A.valuation j₁ →
        sp (Pic0.mk ⟨placeDiff p x (cuspZeroBar p), hzero⟩) = 0)

section WithHeckeModule

variable [iJ : Module HeckeAlg (JZero p)]

def spKernelImage (sp : JZero p →+ T) : AddSubgroup T :=
  (eisensteinKernelSubmodule p iJ).toAddSubgroup.map sp

def RaynaudFor (ℓ : ℕ) (sp : JZero p →+ T) : Prop :=
  ℓ ≠ 2 → ∀ z ∈ eisensteinQuotientRational p iJ,
    (∃ k : ℕ, ℓ ^ k • z = 0) →
    (∀ x : JZero p, eisensteinQuotientMk p iJ x = z → sp x ∈ spKernelImage sp) →
    z = 0

def CuspRuleFor (A : ValuationSubring Qbar) (sp : JZero p →+ T) : Prop :=
  ∀ (x : Place Qbar (modularFunctionFieldBar p)) (j₁ j₂ : Qbar)
      (hinf : placeDiff p x (cuspInftyBar p) ∈ Divisor.degZero)
      (hzero : placeDiff p x (cuspZeroBar p) ∈ Divisor.degZero),
    (∀ σ : Qbar ≃ₐ[ℚ] Qbar, arithmeticGalois (modularFunctionFieldFull p) σ • x = x) →
    0 < x.ord (jBar p - algebraMap Qbar (modularFunctionFieldBar p) j₁) →
    0 < x.ord (jpBar p - algebraMap Qbar (modularFunctionFieldBar p) j₂) →
    1 < A.valuation j₁ →
      (A.valuation j₂ = A.valuation j₁ ^ p →
        sp (Pic0.mk ⟨placeDiff p x (cuspInftyBar p), hinf⟩) ∈ spKernelImage sp) ∧
      (A.valuation j₂ ^ p = A.valuation j₁ →
        sp (Pic0.mk ⟨placeDiff p x (cuspZeroBar p), hzero⟩) ∈ spKernelImage sp)

end WithHeckeModule

end ModularCurve
