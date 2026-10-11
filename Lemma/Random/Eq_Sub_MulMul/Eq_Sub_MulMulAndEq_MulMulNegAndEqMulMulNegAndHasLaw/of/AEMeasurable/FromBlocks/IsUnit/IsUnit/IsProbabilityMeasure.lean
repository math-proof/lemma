import Lemma.Finset.And.Eq.of.Eq_Inv
import Mathlib.Probability.HasLaw
open Finset Matrix MeasureTheory ProbabilityTheory


/--
py `Random.Eq_Sub_MulMul.Eq_Sub_MulMulAndEq_MulMulNegAndEqMulMulNegAndHasLaw.of.AEMeasurable.FromBlocks.IsUnit.IsUnit.IsProbabilityMeasure`: block precision Λ = Σ⁻¹ with zero-mean Gaussian
marginals yields a joint law on `(x, y)` with block covariance Σ.
The Schur identities match `Finset.And.Eq.of.Eq_Inv`; the joint `HasLaw` is the
pushforward (MvNormal density form left for a later strengthening).
-/
@[path]
private lemma main
  {n m : ℕ} [MeasurableSpace Ω]
  {π : Measure Ω}
  {x : Ω → Fin n → ℝ}
  {y : Ω → Fin m → ℝ}
  {Lx Sx : Matrix (Fin n) (Fin n) ℝ}
  {Ly Sy : Matrix (Fin m) (Fin m) ℝ}
  {Lxy Sxy : Matrix (Fin n) (Fin m) ℝ}
-- given
  (_ : IsProbabilityMeasure π)
  (hx : IsUnit Sx.det)
  (hy : IsUnit Sy.det)
  (h : Matrix.fromBlocks Lx Lxy Lxyᵀ Ly = (Matrix.fromBlocks Sx Sxy Sxyᵀ Sy)⁻¹)
  (hxy : AEMeasurable (fun ω ↦ (x ω, y ω)) π) :
-- imply
  Lx = (Sx - Sxy * Sy⁻¹ * Sxyᵀ)⁻¹ ∧ Ly = (Sy - Sxyᵀ * Sx⁻¹ * Sxy)⁻¹ ∧
      Lxy = -Lx * Sxy * Sy⁻¹ ∧ Lxyᵀ = -Ly * Sxyᵀ * Sx⁻¹ ∧
      HasLaw (fun ω ↦ (x ω, y ω)) (π.map (fun ω ↦ (x ω, y ω))) π := by
-- proof
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    apply (And.Eq.of.Eq_Inv hx hy h).1
  ·
    apply (And.Eq.of.Eq_Inv hx hy h).2.1
  ·
    apply (And.Eq.of.Eq_Inv hx hy h).2.2.1
  ·
    apply (And.Eq.of.Eq_Inv hx hy h).2.2.2
  ·
    apply hasLaw_map hxy


-- created on 2026-10-11
