import Lemma.Definitions.Def_ModularCurve_MultCoveringFamily

set_option autoImplicit false

open AlgebraicCurve

namespace ModularCurve.MultCovering

section Link

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

theorem mem_span_range_goodFamily (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) (i : Fin r) :
    s i ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range Φ.t) := by
  rw [Φ.t_basis.2, ← hs.2]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem goodFamily_mem_span_range (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) (j : Fin r) :
    Φ.t j ∈ Submodule.span (AlgebraicClosure ℚ) (Set.range s) := by
  rw [hs.2, ← Φ.t_basis.2]
  exact Submodule.subset_span ⟨j, rfl⟩

noncomputable def linkMatrix (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) :=
  fun i j => (Φ.t_basis.1.repr ⟨s i, mem_span_range_goodFamily Φ s hs i⟩) j

noncomputable def linkMatrixInv (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) :=
  fun i j => (hs.1.repr ⟨Φ.t i, goodFamily_mem_span_range Φ s hs i⟩) j

noncomputable def linkBudget (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) : ℕ :=
  sInf {B : ℕ | ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ i j, (p : AlgebraicClosure ℚ) ^ B * linkMatrix Φ s hs i j ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * linkMatrixInv Φ s hs i j ∈ A}

noncomputable def compConst (Φ : FamCtx p r)
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) : ℝ :=
  4 * ((linkBudget Φ s hs : ℝ) + (modulusExp : ℝ))

theorem linkMatrix_apply (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) (i j : Fin r) :
    linkMatrix Φ s hs i j = (Φ.t_basis.1.repr ⟨s i, mem_span_range_goodFamily Φ s hs i⟩) j := rfl

theorem linkMatrixInv_apply (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) (i j : Fin r) :
    linkMatrixInv Φ s hs i j = (hs.1.repr ⟨Φ.t i, goodFamily_mem_span_range Φ s hs i⟩) j := rfl

theorem compConst_eq (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) : compConst Φ s hs = 4 * ((linkBudget Φ s hs : ℝ) + (modulusExp : ℝ)) := rfl

theorem compConst_nonneg (Φ : FamCtx p r) (s : Fin r → ↥(modularFunctionFieldBar (1 * p)))
    (hs : IsEmbBasis (1 * p) s) : 0 ≤ compConst Φ s hs := by
  unfold compConst; positivity

end Link

end ModularCurve.MultCovering
