import Lemma.Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Lemma.Definitions.Def_ValuationSubring_CompletionRatClosure
import Lemma.Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Mathlib.FieldTheory.Fixed
import Mathlib.Topology.Algebra.Field

set_option autoImplicit false

noncomputable section

open CerednikDrinfeld

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ)) [Fact (A.DecompositionIsometric ℚ)]

theorem smul_completion_eq_self_of_mem_ratClosure (σ : A.decompositionSubgroup ℚ)
    {x : A.valuation.Completion} (hx : x ∈ ratClosure A) : σ • x = x := by

  have hc : IsClosed {y : A.valuation.Completion | σ • y = y} :=
    isClosed_eq (continuous_smul_completion σ) continuous_id
  have hle : ratClosure A ≤ FixedBy.subfield A.valuation.Completion σ :=
    Subfield.topologicalClosure_minimal ⊥ bot_le hc
  exact hle hx

def decompositionToIsometricAut :
    A.decompositionSubgroup ℚ →* Omega.IsometricAut ↥(ratClosure A) A.valuation.Completion where
  toFun σ :=
    { toRingEquiv := completionRingAut σ
      isometry := fun x => valuation_smul_completion σ x
      fix := fun a => smul_completion_eq_self_of_mem_ratClosure A σ a.2 }
  map_one' := by
    apply Omega.IsometricAut.ext
    ext x
    change (1 : ↥(A.decompositionSubgroup ℚ)) • x = x
    exact one_smul _ x
  map_mul' σ τ := by
    apply Omega.IsometricAut.ext
    ext x
    change (σ * τ) • x = σ • (τ • x)
    exact mul_smul σ τ x

@[simp] theorem decompositionToIsometricAut_toRingEquiv_apply (σ : A.decompositionSubgroup ℚ)
    (x : A.valuation.Completion) :
    (decompositionToIsometricAut A σ).toRingEquiv x = σ • x := rfl

theorem decompositionToIsometricAut_toRingEquiv (σ : A.decompositionSubgroup ℚ) :
    (decompositionToIsometricAut A σ).toRingEquiv = completionRingAut σ := rfl

theorem decompositionToIsometricAut_coe (σ : A.decompositionSubgroup ℚ) (a : AlgebraicClosure ℚ) :
    (decompositionToIsometricAut A σ).toRingEquiv ((a : AlgebraicClosure ℚ) : A.valuation.Completion) =
      (((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a : AlgebraicClosure ℚ) : A.valuation.Completion) :=
  smul_completion_coe σ a

theorem decompositionToIsometricAut_toRingEquiv_symm_apply (σ : A.decompositionSubgroup ℚ)
    (x : A.valuation.Completion) :
    (decompositionToIsometricAut A σ).toRingEquiv.symm x = σ⁻¹ • x := by
  rw [← Omega.IsometricAut.inv_toRingEquiv, ← map_inv]
  rfl

end ValuationSubring

end
