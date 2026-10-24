import Lemma.Definitions.Def_ModularCurve_X1

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

variable {L}

theorem isBaseChangeAutOf_baseChangeAut {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    (h : ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ) :
    IsBaseChangeAutOf L σ₀ (baseChangeAut L σ₀) := by
  rw [baseChangeAut, dif_pos h]
  exact h.choose_spec

theorem baseChangeAut_of_not {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    (h : ¬ ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ) :
    baseChangeAut L σ₀ = AlgEquiv.refl := by
  rw [baseChangeAut, dif_neg h]

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

theorem IsDiamondAut.coprime {d : ℕ} {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (h : IsDiamondAut M d σ) : Nat.Coprime d M := h.1

def diamondAut (d : ℕ) : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M :=
  haveI := Classical.dec (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ)
  if h : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ
  then h.choose else AlgEquiv.refl

variable {M}

theorem isDiamondAut_diamondAut {d : ℕ}
    (h : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) :
    IsDiamondAut M d (diamondAut M d) := by
  rw [diamondAut, dif_pos h]
  exact h.choose_spec

theorem diamondAut_of_not {d : ℕ}
    (h : ¬ ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) :
    diamondAut M d = AlgEquiv.refl := by
  rw [diamondAut, dif_neg h]

theorem diamondAut_of_not_coprime {d : ℕ} (h : ¬ Nat.Coprime d M) :
    diamondAut M d = AlgEquiv.refl :=
  diamondAut_of_not fun ⟨_, hσ⟩ => h hσ.coprime

end Diamond

section DiamondBar

variable (M : ℕ)

def diamondAutBar (d : ℕ) :
    x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M :=
  baseChangeAut (AlgebraicClosure ℚ) (diamondAut M d)

def diamondOneBar (d : ℕ) : Module.End ℤ (JOne M) :=
  (DistribSMul.toAddMonoidHom (JOne M) (SemilinearAut.ofAlgAut (diamondAutBar M d))).toIntLinearMap

theorem diamondOneBar_apply (d : ℕ) (x : JOne M) :
    diamondOneBar M d x = SemilinearAut.ofAlgAut (diamondAutBar M d) • x :=
  rfl

end DiamondBar

end ModularCurve

end
