import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.ModularForms.Part5
open ModularEllipticCurve in EllipticCurveLFunction EllipticCurveReduction HeckeOperatorProperties NewformDefinition SpectralTheorem
open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold
open MinimalModel
open Complex Polynomial EllipticCurveReduction
open EllipticCurveLFunction EllipticCurveReduction
open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion
open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularEllipticCurve
open Complex
open EllipticCurveReduction EllipticCurveLFunction
open Complex Asymptotics Filter
open EllipticCurveLFunction Complex
open Complex HeckeAnalyticContinuation
open WeakBSD
open Complex MeasureTheory
open scoped CongruenceSubgroup MatrixGroups ModularForm
open LinearMap IsSymmetric Module.End
open Complex EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularityTheorem HeckeAnalyticContinuation
open Complex HeckeEigenvalueTheorem PeterssonInnerProduct


namespace HeckeOperatorProperties

/--
[scaleLattice_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma scaleLattice_comp
  {l mu : ℂˣ} :
-- imply
  scaleLattice l ∘ scaleLattice mu = scaleLattice (l * mu) := by
-- proof
  funext L
  simp only [Function.comp, scaleLattice]
  ext <;> simp [Units.val_mul, mul_assoc]

end HeckeOperatorProperties

namespace HeckeOperatorProperties

/--
[homothety_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma homothety_mul
  {l mu : ℂˣ} :
-- imply
  homothetyR l * homothetyR mu = homothetyR (l * mu) := by
-- proof
  ext x
  show (FreeAbelianGroup.map (scaleLattice l)) ((FreeAbelianGroup.map (scaleLattice mu)) x) =
    (FreeAbelianGroup.map (scaleLattice (l * mu))) x
  rw [← FreeAbelianGroup.map_comp_apply, scaleLattice_comp]
/-- Multiplicativity of Hecke operators on coprime indices: `T_{mn} = T_m ∘ T_n`
when `gcd(m, n) = 1`. -/
end HeckeOperatorProperties
namespace HeckeMultiplicativity
open Complex
/-- The Hecke operator `T_n` acting on modular forms of weight `k` for
`SL(2, ℤ)`. -/
end HeckeMultiplicativity
namespace GaloisRepresentation
open EllipticCurveReduction EllipticCurveLFunction


namespace NewformDefinition

/--
[DirichletSeries.eval_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma DirichletSeries.eval_eq
  {L : DirichletSeries}
  {s : ℂ} :
-- imply
  L.eval s = LSeries L.coeffs s :=
-- proof
  rfl

end NewformDefinition

namespace NewformDefinition

/--
[DirichletSeries.summable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma DirichletSeries.summable_iff
  {L : DirichletSeries}
  {s : ℂ} :
-- imply
  L.summable s ↔ LSeriesSummable L.coeffs s :=
-- proof
  Iff.rfl

end NewformDefinition

namespace NewformDefinition

/--
[DirichletSeries.summable_of_isBigO_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma DirichletSeries.summable_of_isBigO_rpow
  {L : DirichletSeries}
  {σ : ℝ}
  {s : ℂ}
-- given
  (hs : σ + 1 < s.re)
  (hO : L.coeffs =O[atTop] fun n : ℕ => (n : ℝ) ^ σ) :
-- imply
  L.summable s := by
-- proof
  apply LSeriesSummable_of_isBigO_rpow (x := σ + 1) hs
  simp only [add_sub_cancel_right]
  exact hO

end NewformDefinition

namespace NewformDefinition

/--
[DirichletSeries.differentiableOn_of_isBigO_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma DirichletSeries.differentiableOn_of_isBigO_rpow
  {L : DirichletSeries}
  {σ : ℝ}
-- given
  (hO : L.coeffs =O[atTop] fun n : ℕ => (n : ℝ) ^ σ) :
-- imply
  DifferentiableOn ℂ L.eval {s | σ + 1 < s.re} := by
-- proof
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have hab : LSeries.abscissaOfAbsConv L.coeffs ≤ σ + 1 :=
    LSeries.abscissaOfAbsConv_le_of_isBigO_rpow hO
  have hlt : LSeries.abscissaOfAbsConv L.coeffs < ↑s.re := by
    exact lt_of_le_of_lt hab (by exact_mod_cast hs)
  exact (LSeries_hasDerivAt hlt).differentiableAt
end NewformDefinition
namespace WeakBSD
open EllipticCurveLFunction Complex


namespace SpectralTheorem

/--
[spectral_theorem_commuting_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma spectral_theorem_commuting_symmetric
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [DecidableEq (ι → 𝕜)]
  {T : ι → E →ₗ[𝕜] E}
-- given
  (hT : ∀ i, (T i).IsSymmetric)
  (hC : Pairwise (Function.onFun Commute T)) :
-- imply
  DirectSum.IsInternal (fun χ : ι → 𝕜 ↦ ⨅ j, eigenspace (T j) (χ j)) :=
-- proof
  LinearMap.IsSymmetric.directSum_isInternal_of_pairwise_commute hT hC

end SpectralTheorem

namespace SpectralTheorem

/--
[spectral_theorem_commuting_symmetric_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma spectral_theorem_commuting_symmetric_iSup
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {T : ι → E →ₗ[𝕜] E}
-- given
  (hT : ∀ i, (T i).IsSymmetric)
  (hC : Pairwise (Function.onFun Commute T)) :
-- imply
  ⨆ χ : ι → 𝕜, ⨅ i, eigenspace (T i) (χ i) = ⊤ :=
-- proof
  iSup_iInf_eq_top_of_commute hT hC

end SpectralTheorem

namespace SpectralTheorem

/--
[directSum_isInternal_commuting_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean)
-/
@[path]
lemma directSum_isInternal_commuting_pair
  [RCLike 𝕜]
  [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  {A B : E →ₗ[𝕜] E}
-- given
  (hA : A.IsSymmetric)
  (hB : B.IsSymmetric)
  (hAB : Commute A B) :
-- imply
  DirectSum.IsInternal (fun (i : 𝕜 × 𝕜) ↦ (eigenspace A i.2 ⊓ eigenspace B i.1)) :=
-- proof
  directSum_isInternal_of_commute hA hB hAB
end SpectralTheorem
namespace LFunctionAnalyticContinuation
open Complex EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularityTheorem HeckeAnalyticContinuation



-- created on 2026-10-23
