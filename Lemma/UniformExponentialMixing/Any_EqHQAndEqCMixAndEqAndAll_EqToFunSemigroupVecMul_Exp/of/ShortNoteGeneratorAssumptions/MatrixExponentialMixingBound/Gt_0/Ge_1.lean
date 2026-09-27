import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import sympy.stats.frozen_invariant_law
import sympy.Basic
import Lemma.NormedSpace.HasDerivAtVecMul_Exp
import Lemma.GeneratorMatrix.RowStochastic_Exp.of.Ge_0.GeneratorMatrix
import Lemma.NormedSpace.EqVecMul_Exp.of.EqVecMul_0
import Lemma.NormedSpace.VecMul.eq.Zero.of.All_EqVecMul_Exp
open Matrix NormedSpace


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {d : ℕ}
  {r : ℝ}
  {Q : EuclideanVec d → Matrix S S ℝ}
  {cMix γ : ℝ}
-- given
  (h₀ : 1 ≤ cMix)
  (h₁ : 0 < γ)
  (h₂ : MatrixExponentialMixingBound r Q cMix γ)
  (hQ : ShortNoteGeneratorAssumptions r Q) :
-- imply
  ∃ hMix : UniformExponentialMixing r Q, hMix.hQ = hQ ∧ hMix.cMix = cMix ∧ hMix.γ = γ ∧ ∀ θ t ξ, hMix.semigroup.toFun θ t ξ = ξ ᵥ* exp (t • Q θ) := by
-- proof
  let T : EuclideanVec d → ℝ → (S → ℝ) →L[ℝ] (S → ℝ) := fun θ t => LinearMap.toContinuousLinearMap (Matrix.vecMulLinear (exp (t • Q θ)))
  have hT : ∀ θ t ξ, T θ t ξ = ξ ᵥ* exp (t • Q θ) := fun _ _ _ => rfl
  refine ⟨{
    hQ := hQ
    cMix := cMix
    γ := γ
    cMix_ge_one := h₀
    γ_pos := h₁
    semigroup := {
      toFun := T
      map_zero' := fun θ => by
        ext1 ξ
        simp [hT]
      map_add' := fun θ t s _ _ => by
        ext1 ξ
        simp only [hT, ContinuousLinearMap.comp_apply, Matrix.vecMul_vecMul]
        rw [add_comm t s, add_smul, Matrix.exp_add_of_commute _ _ (((Commute.refl (Q θ)).smul_left s).smul_right t)]
      preserves_simplex := fun θ hθ μ hμ t ht => by
        have := GeneratorMatrix.RowStochastic_Exp.of.Ge_0.GeneratorMatrix (hQ.generator_on_box θ hθ) ht
        rw [hT]
        infer_instance
      fixed_iff_invariantLaw := fun θ hθ μ hμ => by
        simp only [hT]
        exact ⟨fun h => ⟨NormedSpace.VecMul.eq.Zero.of.All_EqVecMul_Exp h⟩, fun h t _ => NormedSpace.EqVecMul_Exp.of.EqVecMul_0 h.invariant t⟩ }
    solves_equation := fun θ hθ ξ => by
      refine ⟨continuous_iff_continuousAt.2 fun t => (NormedSpace.HasDerivAtVecMul_Exp (Q θ) ξ t).continuousAt, fun t _ => ?_⟩
      simpa [hT] using (NormedSpace.HasDerivAtVecMul_Exp (Q θ) ξ t).hasDerivWithinAt
    mixing := fun θ hθ ξ hξ t ht => by simpa [hT] using h₂.bound θ hθ ξ hξ t ht }, rfl, rfl, rfl, hT⟩


-- created on 2026-09-26
