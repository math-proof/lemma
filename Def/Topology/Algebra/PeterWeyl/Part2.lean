/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Algebra/PeterWeyl.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Instance.Topology.Algebra.PeterWeyl

@[expose] public section

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
