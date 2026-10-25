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
import Theorem.Topology.Algebra.PeterWeyl.Part2


noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- `T0` as a linear map into `C(G, ℂ)`. -/
noncomputable def pwT0Lin (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →ₗ[ℂ] C(G, ℂ) :=
  { toFun := fun f => pwT0Map (G := G) k f
    map_add' := by
      intro f g
      ext t
      simp only [pwT0Map_apply, ContinuousMap.add_apply]
      exact inner_add_right _ _ _
    map_smul' := by
      intro c f
      ext t
      simp only [pwT0Map_apply, ContinuousMap.smul_apply]
      exact inner_smul_right _ _ _ }

/-- `T0` as a continuous linear map into `C(G, ℂ)`. -/
noncomputable def pwT0 (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →L[ℂ] C(G, ℂ) :=
  (pwT0Lin (G := G) k).mkContinuousOfExistsBound (by
    obtain ⟨C, hC0, hC⟩ := pwPhi_bound (G := G) k
    refine ⟨C, fun f => ?_⟩
    change ‖pwT0Map (G := G) k f‖ ≤ C * ‖f‖
    rw [ContinuousMap.norm_le _ (mul_nonneg hC0 (norm_nonneg f))]
    intro g
    rw [pwT0Map_apply]
    calc ‖⟪pwPhi (G := G) k g, f⟫‖ ≤ ‖pwPhi (G := G) k g‖ * ‖f‖ :=
          norm_inner_le_norm _ _
      _ ≤ C * ‖f‖ := mul_le_mul_of_nonneg_right (hC g) (norm_nonneg f))

/-- `T` is `toLp` after `T0`. -/
noncomputable def pwT (k : C(G, ℂ)) :
    (Lp ℂ 2 (pwHaar G)) →L[ℂ] Lp ℂ 2 (pwHaar G) :=
  (ContinuousMap.toLp 2 (pwHaar G) ℂ).comp (pwT0 (G := G) k)

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
