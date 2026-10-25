/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Geometry.Manifold.Instances.Sphere
import Lemma.Set.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open scoped Manifold ContDiff Topology Bundle


section LocalDiffeomorphConstructors

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

end LocalDiffeomorphConstructors
section IntervalParametrisation
end IntervalParametrisation
section InverseFunction1D
end InverseFunction1D
noncomputable section

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

section SpeedSetup

/-- Squared speed of a curve `γ : ℝ → M` at `t`, measured with the metric `g`.
If `γ` is not differentiable at `t`, `mfderiv` is `0`, so the speed is `0`. -/
def omCurveSpeedSq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))

/-- The constant-velocity section `s ↦ (s, 1)` into `ModelProd ℝ ℝ`, with the
`ModelProd` codomain so that smoothness statements resolve the `chartedSpaceSelf`
instance (matching `tangentBundleModelSpaceHomeomorph`). -/
def omPairFn : ℝ → ModelProd ℝ ℝ := fun s => (s, (1 : ℝ))

/-- `γ` has unit speed on `U`: it is smooth and its squared speed is `1`. -/
def omIsUnitSpeedOn
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ U ∧ ∀ t ∈ U, omCurveSpeedSq g γ t = 1

end SpeedSetup

section ArcLengthIntegral

end ArcLengthIntegral

section UnitSpeedCharts

/-- The linear identification `ℝ ≃L[ℝ] E1`. -/
def omLinEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm

end UnitSpeedCharts

section IdentityTheorem

end IdentityTheorem

section MaximalCurve

/-- An admissible pair: an open connected neighbourhood of `0` carrying a
unit-speed curve that agrees with the base chart near `0`. -/
def omAdmissible
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞) (J : Set ℝ) (δ : ℝ → M) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ omIsUnitSpeedOn g δ J ∧ δ =ᶠ[nhds 0] ⇑α0

end MaximalCurve

section AbsorbMaximal

end AbsorbMaximal

section OntoMaximal

end OntoMaximal

section PeriodicCoincidence

end PeriodicCoincidence

section MinimalPeriod

end MinimalPeriod

section CircleExpLocalDiffeo

end CircleExpLocalDiffeo

section PeriodicCase

end PeriodicCase

section BoundaryInterior

/-- The inclusion of the open half of `H` into `E1`, as an open partial homeomorphism.
Its target is the interior of the range of `𝓡∂ 1`. -/
def omb_interiorModelHomeomorph :
    OpenPartialHomeomorph (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1)) :=
  OpenPartialHomeomorph.mk
    (PartialHomeomorph.mk
      { toFun := Subtype.val
        invFun := (𝓡∂ 1).symm
        source := {y | 0 < (y.val) 0}
        target := {y | 0 < y 0}
        map_source' := fun _ hy => hy
        map_target' := by
          intro y hy
          have hy' : 0 < y.ofLp 0 := hy
          change 0 < (((𝓡∂ 1).symm y).val) 0
          rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hy')]
          exact hy'
        left_inv' := by
          intro y _
          exact ModelWithCorners.left_inv (𝓡∂ 1) y
        right_inv' := by
          intro y hy
          have hy' : 0 < y.ofLp 0 := hy
          have hle : 0 ≤ y.ofLp 0 := le_of_lt hy'
          have hmem : y ∈ Set.range (𝓡∂ 1) := by
            rw [range_modelWithCornersEuclideanHalfSpace]
            exact hle
          have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
          simpa using h }
      (continuous_subtype_val.continuousOn)
      ((ModelWithCorners.continuous_symm (𝓡∂ 1)).continuousOn))
    ((PiLp.continuous_apply 2 _ 0 |>.comp continuous_subtype_val).isOpen_preimage _
      isOpen_Ioi)
    ((PiLp.continuous_apply 2 _ 0).isOpen_preimage _ isOpen_Ioi)

/-- The interior of `M` as an open subset. -/
def ombInterior : TopologicalSpace.Opens M :=
  ⟨(𝓡∂ 1).interior M, (𝓡∂ 1).isOpen_interior (by simp : (∞ : ℕ∞ω) ≠ 0)⟩

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
