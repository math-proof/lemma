import Lemma.ModularCurve.X1

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section BaseChangeAut

variable (L : Type*) [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

def IsBaseChangeAutOf (σ₀ : F₀ ≃ₐ[ℚ] F₀)
    (σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀) : Prop :=
  ∀ y : F₀,
    ((σ ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩ :
        laurentBaseChange L F₀) : LaurentSeries L)
      = coeffEmb L ((σ₀ y : F₀) : LaurentSeries ℚ)

def baseChangeAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) :
    laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀ :=
  haveI := Classical.dec
    (∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ)
  if h : ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ
  then h.choose else AlgEquiv.refl

end BaseChangeAut

section Diamond

variable (M : ℕ)

def slashQExpC (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))

def IsDiamondAut (d : ℕ) (σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) : Prop :=
  Nat.Coprime d M ∧
    ∀ (k : ℤ) (f g : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
      (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
        coeffMap (algebraMap ℚ ℂ)
            ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                x1FunctionField M) : LaurentSeries ℚ)
          * slashQExpC k g γ = slashQExpC k f γ


def diamondAut (d : ℕ) : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M :=
  haveI := Classical.dec (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ)
  if h : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ
  then h.choose else AlgEquiv.refl

end Diamond

section DiamondBar

variable (M : ℕ)

def diamondAutBar (d : ℕ) :
    x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M :=
  baseChangeAut (AlgebraicClosure ℚ) (diamondAut M d)

def diamondOneBar (d : ℕ) : Module.End ℤ (JOne M) :=
  (DistribSMul.toAddMonoidHom (JOne M) (SemilinearAut.ofAlgAut (diamondAutBar M d))).toIntLinearMap

end DiamondBar

end ModularCurve

end
