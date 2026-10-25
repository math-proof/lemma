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
import Instance.Topology.Algebra.PeterWeyl


noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- Left translation on `L²(G, μ; ℂ)`: `(pwTransl g f) x = f (g⁻¹ * x)` a.e. -/
noncomputable def pwTransl (g : G) :
    Lp ℂ 2 (pwHaar G) →ₗᵢ[ℂ] Lp ℂ 2 (pwHaar G) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x => g⁻¹ * x)
    (measurePreserving_mul_left (pwHaar G) g⁻¹)

/-- Kernel section at `g`: the continuous map `h ↦ conj (k (h⁻¹ * g))`. -/
noncomputable def pwPhiKer (k : C(G, ℂ)) (g : G) : C(G, ℂ) :=
  ⟨fun h => conj (k (h⁻¹ * g)),
    Complex.continuous_conj.comp
      (k.continuous.comp (continuous_id.inv.mul_const g))⟩

/-- `Φ g` is the kernel section viewed in `L²`. -/
noncomputable def pwPhi (k : C(G, ℂ)) (g : G) : Lp ℂ 2 (pwHaar G) :=
  ContinuousMap.toLp 2 (pwHaar G) ℂ (pwPhiKer (G := G) k g)

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
