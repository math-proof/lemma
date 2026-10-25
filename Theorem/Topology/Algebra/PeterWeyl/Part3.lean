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
import Def.Topology.Algebra.PeterWeyl.Part4


noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Integral formula for `T0` applied to a continuous function. -/
theorem pwT0_toLp_apply (k k' : C(G, ℂ)) (g : G) :
    (pwT0Map (G := G) k (ContinuousMap.toLp 2 (pwHaar G) ℂ k')) g
      = ∫ h, k' h * k (h⁻¹ * g) ∂(pwHaar G) := by
  rw [pwT0Map_apply]
  change ⟪ContinuousMap.toLp 2 (pwHaar G) ℂ (pwPhiKer (G := G) k g),
    ContinuousMap.toLp 2 (pwHaar G) ℂ k'⟫ = _
  rw [MeasureTheory.ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  simp only [pwPhiKer_apply]
  rw [Complex.conj_conj]

/-- Lipschitz estimate for values of `T0 f`. -/
theorem pwT0_lipschitz (k : C(G, ℂ)) (f : Lp ℂ 2 (pwHaar G)) (g g' : G) :
    ‖(pwT0Map (G := G) k f) g - (pwT0Map (G := G) k f) g'‖
      ≤ ‖pwPhi (G := G) k g - pwPhi (G := G) k g'‖ * ‖f‖ := by
  rw [pwT0Map_apply, pwT0Map_apply, ← inner_sub_left]
  exact norm_inner_le_norm _ _

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
