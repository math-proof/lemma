/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Algebra.Monoid
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Def.Topology.Algebra.PeterWeyl.Part5


noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Values of members of `pwA k` lie in the closed ball of radius `C`. -/
theorem pwA_values (k : C(G, ℂ)) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ g : G, ‖pwPhi (G := G) k g‖ ≤ C) (Y : G →ᵇ ℂ) (hY : Y ∈ pwA (G := G) k)
    (x : G) : Y x ∈ Metric.closedBall (0 : ℂ) C := by
  obtain ⟨f, hfball, hfx⟩ := pwA_mem_obtain (G := G) k Y hY
  have hfnorm : ‖f‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hfball
    rwa [dist_eq_norm, sub_zero] at h
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hfx]
  rw [pwT0Map_apply]
  calc ‖⟪pwPhi (G := G) k x, f⟫‖ ≤ ‖pwPhi (G := G) k x‖ * ‖f‖ :=
        norm_inner_le_norm _ _
    _ ≤ C * 1 := mul_le_mul (hC x) hfnorm (norm_nonneg _) hC0
    _ = C := mul_one _

/-- The family `pwA k` is equicontinuous. -/
theorem pwA_equicontinuous (k : C(G, ℂ)) :
    Equicontinuous (fun x : ↥(pwA (G := G) k) => ⇑(↑x : G →ᵇ ℂ)) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hcont : ContinuousAt (pwPhi (G := G) k) x₀ :=
    (pwPhi_continuous (G := G) k).continuousAt
  have hΦ : ∀ᶠ x : G in nhds x₀,
      dist (pwPhi (G := G) k x) (pwPhi (G := G) k x₀) < ε :=
    hcont.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hΦ] with x hx i
  obtain ⟨f, hfball, hfx⟩ := pwA_mem_obtain (G := G) k _ i.property
  have hfnorm : ‖f‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp hfball
    rwa [dist_eq_norm, sub_zero] at h
  have e1 : dist ((↑i : G →ᵇ ℂ) x₀) ((↑i : G →ᵇ ℂ) x)
      ≤ dist (pwPhi (G := G) k x₀) (pwPhi (G := G) k x) := by
    simp only [hfx]
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖(pwT0Map (G := G) k f) x₀ - (pwT0Map (G := G) k f) x‖
        ≤ ‖pwPhi (G := G) k x₀ - pwPhi (G := G) k x‖ * ‖f‖ :=
          pwT0_lipschitz (G := G) k f x₀ x
      _ ≤ ‖pwPhi (G := G) k x₀ - pwPhi (G := G) k x‖ * 1 :=
        mul_le_mul_of_nonneg_left hfnorm (norm_nonneg _)
      _ = ‖pwPhi (G := G) k x₀ - pwPhi (G := G) k x‖ := mul_one _
  calc dist ((↑i : G →ᵇ ℂ) x₀) ((↑i : G →ᵇ ℂ) x)
      ≤ dist (pwPhi (G := G) k x₀) (pwPhi (G := G) k x) := e1
    _ = dist (pwPhi (G := G) k x) (pwPhi (G := G) k x₀) := dist_comm _ _
    _ < ε := hx

/-- `T` is a compact operator, via Arzelà–Ascoli. -/
theorem pwT_compact (k : C(G, ℂ)) :
    IsCompactOperator ⇑(pwT (G := G) k) := by
  obtain ⟨C, hC0, hC⟩ := pwPhi_bound (G := G) k
  have hA : ∀ Y : G →ᵇ ℂ, ∀ x : G, Y ∈ pwA (G := G) k →
      Y x ∈ Metric.closedBall (0 : ℂ) C :=
    fun Y x hY => pwA_values (G := G) k C hC0 hC Y hY x
  have hclosure : IsCompact (closure (pwA (G := G) k)) :=
    BoundedContinuousFunction.arzela_ascoli _ (isCompact_closedBall 0 C) _ hA
      (pwA_equicontinuous (G := G) k)
  have hK : IsCompact (⇑(ContinuousMap.toLp 2 (pwHaar G) ℂ) ''
      (⇑(ContinuousMap.isometryEquivBoundedOfCompact G ℂ).symm ''
        closure (pwA (G := G) k))) :=
    (hclosure.image
      (ContinuousMap.isometryEquivBoundedOfCompact G ℂ).symm.continuous).image
      (ContinuousMap.toLp 2 (pwHaar G) ℂ).continuous
  have hTf : ∀ f : Lp ℂ 2 (pwHaar G),
      (pwT0 (G := G) k) f = pwT0Map (G := G) k f :=
    fun f => LinearMap.mkContinuousOfExistsBound_apply _ _ f
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.closedBall (0 : Lp ℂ 2 (pwHaar G)) 1,
    Metric.closedBall_mem_nhds 0 one_pos, _, hK, ?_⟩
  intro y hy
  obtain ⟨f, hfball, rfl⟩ := hy
  refine ⟨(pwT0 (G := G) k) f,
    ⟨(ContinuousMap.isometryEquivBoundedOfCompact G ℂ) (pwT0Map (G := G) k f),
      ?_, ?_⟩, rfl⟩
  · exact subset_closure ⟨pwT0Map (G := G) k f, ⟨f, hfball, rfl⟩, rfl⟩
  · rw [IsometryEquiv.symm_apply_apply]
    exact (hTf f).symm

/-- `T` commutes with every left translation. -/
theorem pwT_comm (k : C(G, ℂ)) (a : G) (f : Lp ℂ 2 (pwHaar G)) :
    (pwT (G := G) k) (pwTransl (G := G) a f)
      = pwTransl (G := G) a ((pwT (G := G) k) f) := by
  have hT0eq : pwT0Map (G := G) k (pwTransl (G := G) a f)
      = (pwT0Map (G := G) k f).comp ⟨fun t => a⁻¹ * t, continuous_const_mul a⁻¹⟩ := by
    apply ContinuousMap.ext
    intro g
    simp only [ContinuousMap.comp_apply, pwT0Map_apply]
    change ⟪pwPhi (G := G) k g, pwTransl (G := G) a f⟫
      = ⟪pwPhi (G := G) k (a⁻¹ * g), f⟫
    rw [pwTransl_inner' (G := G) a _ f, pwTransl_Phi (G := G) k a g]
  have hTf : ∀ x : Lp ℂ 2 (pwHaar G),
      (pwT0 (G := G) k) x = pwT0Map (G := G) k x :=
    fun x => LinearMap.mkContinuousOfExistsBound_apply _ _ x
  have hTT : ∀ x : Lp ℂ 2 (pwHaar G),
      (pwT (G := G) k) x
        = ContinuousMap.toLp 2 (pwHaar G) ℂ ((pwT0 (G := G) k) x) := fun x => rfl
  rw [hTT, hTT, hTf, hTf, hT0eq, ← pwTransl_toLp]

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
