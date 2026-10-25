import Lemma.ModularCurve.XHHeckeOperator
import Lemma.CohCarrier.Inst

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def IsDiamondAutHBar (d : (ZMod M)ˣ)
    (σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
        ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H) :
            LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

def diamondAutHBar (d : (ZMod M)ˣ) :
    xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H :=
  haveI := Classical.dec (∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
    IsDiamondAutHBar M H d σ)
  if h : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ
  then h.choose else AlgEquiv.refl

variable {M H}


variable (M H)

def diamondHBar (d : (ZMod M)ˣ) : JH M H →+ JH M H :=
  DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut (diamondAutHBar M H d))

end Diamond

section GenOp

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)

def genOpH : CohCarrier.Gen M S → (JH M H →+ JH M H)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H q
  | .dia d => diamondHBar M H d


variable (p : ℕ) [Fact p.Prime]

def tateGenOpH (g : CohCarrier.Gen M S) : Module.End ℤ_[p] (TateModule p (JH M H)) :=
  JH.tateEnd M H p (genOpH M H S g)

end GenOp

section Inputs

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def HeckeDiamondInputsHAll : Prop :=
  (∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ) ∧
    ∀ d : (ZMod M)ˣ, ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ

end Inputs

end ModularCurve

end
