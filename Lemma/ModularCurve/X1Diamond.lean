import Lemma.ModularCurve.X1
import Def.ModularCurve_X1Diamond

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section BaseChangeAut

variable (L : Type*) [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}


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


theorem IsDiamondAut.coprime {d : ℕ} {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (h : IsDiamondAut M d σ) : Nat.Coprime d M := h.1


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


theorem diamondOneBar_apply (d : ℕ) (x : JOne M) :
    diamondOneBar M d x = SemilinearAut.ofAlgAut (diamondAutBar M d) • x :=
  rfl

end DiamondBar

end ModularCurve

end
