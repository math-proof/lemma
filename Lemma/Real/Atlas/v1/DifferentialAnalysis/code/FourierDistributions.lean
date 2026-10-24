import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.FourierDistributions
open MeasureTheory FourierDistributions
open scoped SchwartzMap FourierTransform
open TemperedDistribution LineDeriv


namespace FourierDistributions

/--
[fourierDistrib_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourierDistrib_apply
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)}
  {φ : 𝓢(V, ℂ)} :
-- imply
  (𝓕 u) φ = u (𝓕 φ) :=
-- proof
  rfl

end FourierDistributions

namespace FourierDistributions

/--
[fourier_tempDistrib_isomorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourier_tempDistrib_isomorphism
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] :
-- imply
  ∃ e : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ), (∀ u, e u = 𝓕 u) ∧ (∀ u, e.symm u = 𝓕⁻ u) :=
-- proof
  ⟨fourierTempDistribCLE,
    fun u => FourierTransform.fourierCLE_apply u,
    fun u => FourierTransform.fourierCLE_symm_apply u⟩

end FourierDistributions

namespace FourierDistributions

/--
[fourierTempDistribCLE_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourierTempDistribCLE_apply
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)} :
-- imply
  fourierTempDistribCLE u = 𝓕 u :=
-- proof
  FourierTransform.fourierCLE_apply u

end FourierDistributions

namespace FourierDistributions

/--
[fourierTempDistribCLE_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourierTempDistribCLE_symm_apply
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)} :
-- imply
  fourierTempDistribCLE.symm u = 𝓕⁻ u :=
-- proof
  FourierTransform.fourierCLE_symm_apply u
open TemperedDistribution LineDeriv

end FourierDistributions

namespace FourierDistributions

/--
[fourier_lineDeriv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourier_lineDeriv_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)}
  {m : V} :
-- imply
  𝓕 (∂_{m} u) = (2 * Real.pi * Complex.I) • smulLeftCLM ℂ (inner ℝ · m) (𝓕 u) :=
-- proof
  TemperedDistribution.fourier_lineDerivOp_eq u m

end FourierDistributions

namespace FourierDistributions

/--
[lineDeriv_fourier_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma lineDeriv_fourier_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)}
  {m : V} :
-- imply
  ∂_{m} (𝓕 u) = 𝓕 (-(2 * Real.pi * Complex.I) • smulLeftCLM ℂ (inner ℝ · m) u) :=
-- proof
  TemperedDistribution.lineDerivOp_fourier_eq u m

end FourierDistributions

namespace FourierDistributions

/--
[iteratedMulOp_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma iteratedMulOp_zero
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {m : Fin 0 → V}
  {u : 𝓢'(V, ℂ)} :
-- imply
  iteratedMulOp m u = u :=
-- proof
  rfl

end FourierDistributions

namespace FourierDistributions

/--
[fourier_iteratedLineDerivOp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourier_iteratedLineDerivOp_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)}
  {n : ℕ}
  {m : Fin n → V} :
-- imply
  𝓕 (∂^{m} u) = (2 * Real.pi * Complex.I) ^ n • iteratedMulOp m (𝓕 u) := by
-- proof
  induction n with
  | zero => simp [iteratedLineDerivOp_fin_zero, iteratedMulOp]
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, TemperedDistribution.fourier_lineDerivOp_eq,
      IH (Fin.tail m)]
    simp only [iteratedMulOp, map_smul, smul_smul, pow_succ]
    ring_nf

end FourierDistributions

namespace FourierDistributions

/--
[iteratedLineDerivOp_fourier_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma iteratedLineDerivOp_fourier_eq
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {u : 𝓢'(V, ℂ)}
  {n : ℕ}
  {m : Fin n → V} :
-- imply
  ∂^{m} (𝓕 u) = 𝓕 ((-(2 * Real.pi * Complex.I)) ^ n • iteratedMulOp m u) := by
-- proof
  induction n with
  | zero => simp [iteratedLineDerivOp_fin_zero, iteratedMulOp]
  | succ n IH =>
    rw [iteratedLineDerivOp_succ_left, IH (Fin.tail m),
      TemperedDistribution.lineDerivOp_fourier_eq]
    simp only [iteratedMulOp, map_smul, smul_smul, pow_succ]
    ring_nf

end FourierDistributions

namespace FourierDistributions

/--
[fourier_tempDistrib_multiindex_exchange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierDistributions.lean)
-/
@[path]
lemma fourier_tempDistrib_multiindex_exchange
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] :
-- imply
  (∃ e : 𝓢'(V, ℂ) ≃L[ℂ] 𝓢'(V, ℂ), (∀ u, e u = 𝓕 u) ∧ (∀ u, e.symm u = 𝓕⁻ u)) ∧ (∀ (u : 𝓢'(V, ℂ)) {n : ℕ} (m : Fin n → V), 𝓕 (∂^{m} u) = (2 * Real.pi * Complex.I) ^ n • iteratedMulOp m (𝓕 u)) ∧ (∀ (u : 𝓢'(V, ℂ)) {n : ℕ} (m : Fin n → V), ∂^{m} (𝓕 u) = 𝓕 ((-(2 * Real.pi * Complex.I)) ^ n • iteratedMulOp m u)) :=
-- proof
  ⟨fourier_tempDistrib_isomorphism, fourier_iteratedLineDerivOp_eq,
    iteratedLineDerivOp_fourier_eq⟩
end FourierDistributions



-- created on 2026-10-23
