import Lemma.Definitions.Def_ModularCurve_Eisenstein
import Lemma.Definitions.Def_ModularCurve_MazurStepThree

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable (p : ℕ) [NeZero p]

def eisensteinKernelSubmodule (inst : Module HeckeAlg (JZero p)) :
    letI := inst; Submodule HeckeAlg (JZero p) :=
  letI := inst
  eisensteinKernel (JZero p) (eisensteinIdeal p) • (⊤ : Submodule HeckeAlg (JZero p))

abbrev EisensteinQuotient (inst : Module HeckeAlg (JZero p)) : Type :=
  letI := inst
  JZero p ⧸ eisensteinKernelSubmodule p inst

def eisensteinQuotientMk (inst : Module HeckeAlg (JZero p)) :
    JZero p →+ EisensteinQuotient p inst :=
  letI := inst
  (eisensteinKernelSubmodule p inst).mkQ.toAddMonoidHom

def eisensteinQuotientRational (inst : Module HeckeAlg (JZero p)) :
    Set (EisensteinQuotient p inst) :=
  letI := inst
  eisensteinQuotientMk p inst ''
    {x : JZero p | ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      σ • x - x ∈ eisensteinKernelSubmodule p inst}

theorem eisensteinQuotientInvariantsFiniteAt_iff (inst : Module HeckeAlg (JZero p)) :
    EisensteinQuotientInvariantsFiniteAt p inst ↔ (eisensteinQuotientRational p inst).Finite :=
  Iff.rfl

def CuspidalClassSurvives (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  cuspidalClass p ∉ eisensteinKernelSubmodule p inst

abbrev jBar : modularFunctionFieldBar p :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full p)⟩

abbrev jpBar : modularFunctionFieldBar p :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full p (dvd_refl p))⟩

def placeDiff (x y : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
  Finsupp.single x 1 - Finsupp.single y 1

def MazurQuotientSpecialization (inst : Module HeckeAlg (JZero p)) : Prop :=
  letI := inst
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∃ (T : Type) (_ : AddCommGroup T) (s : EisensteinQuotient p inst →+ T),
        (∀ z ∈ eisensteinQuotientRational p inst,
            (∃ m : ℕ, ¬ ℓ ∣ m ∧ m • z = 0) → s z = 0 → z = 0) ∧
        (ℓ ≠ 2 → ∀ z ∈ eisensteinQuotientRational p inst,
            (∃ k : ℕ, ℓ ^ k • z = 0) → s z = 0 → z = 0) ∧
        (∀ (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
            (j₁ j₂ : AlgebraicClosure ℚ)
            (hinf : placeDiff p x (cuspInftyBar p) ∈ Divisor.degZero)
            (hzero : placeDiff p x (cuspZeroBar p) ∈ Divisor.degZero),
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
              arithmeticGalois (modularFunctionFieldFull p) σ • x = x) →
          0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₁) →
          0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) j₂) →
          1 < A.valuation j₁ →
            (A.valuation j₂ = A.valuation j₁ ^ p →
              s (eisensteinQuotientMk p inst
                (Pic0.mk ⟨placeDiff p x (cuspInftyBar p), hinf⟩)) = 0) ∧
            (A.valuation j₂ ^ p = A.valuation j₁ →
              s (eisensteinQuotientMk p inst
                (Pic0.mk ⟨placeDiff p x (cuspZeroBar p), hzero⟩)) = 0))

end ModularCurve

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

variable (p : ℕ) [NeZero p]

def jInt (W : WeierstrassCurve ℤ) : AlgebraicClosure ℚ :=
  ((W.c₄ : ℤ) : AlgebraicClosure ℚ) ^ 3 / ((W.Δ : ℤ) : AlgebraicClosure ℚ)

abbrev JQuot : Type :=
  (W : WeierstrassCurve ℤ) → ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point →
    AlgebraicClosure ℚ

def ModuliPointExists (jQuot : JQuot) : Prop :=
  p.Prime →
  ∀ (W : WeierstrassCurve ℤ), W.Δ ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄) →
    ∀ (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) →
      addOrderOf Q = p →
      ∃ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
        x.deg = 1 ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
            arithmeticGalois (modularFunctionFieldFull p) σ • x = x) ∧
        0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (jInt W)) ∧
        0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p)
              (jQuot W Q))

def TateCuspCriterion (jQuot : JQuot) : Prop :=
  p.Prime →
  ∀ (W : WeierstrassCurve ℤ), W.Δ ≠ 0 →
    ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → (ℓ : ℤ) ∣ W.Δ → ¬ (ℓ : ℤ) ∣ W.c₄ →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
    ∀ (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) →
      addOrderOf Q = p →
        1 < A.valuation (jInt W) ∧
        (W.InZeroComponentAt A Q → A.valuation (jQuot W Q) = A.valuation (jInt W) ^ p) ∧
        (¬ W.InZeroComponentAt A Q → A.valuation (jQuot W Q) ^ p = A.valuation (jInt W))

end ModularCurve

end
