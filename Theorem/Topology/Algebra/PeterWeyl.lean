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
public import Def.Topology.Algebra.PeterWeyl.Part2

public section

noncomputable section

namespace MathlibExt.Topology.Algebra.PeterWeylWanted

open MeasureTheory

open scoped ComplexInnerProductSpace ComplexConjugate BoundedContinuousFunction

section PWHelpers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- `Φ` is continuous in `g`. -/
theorem pwPhi_continuous (k : C(G, ℂ)) :
    Continuous (pwPhi (G := G) k) := by
  have hK : Continuous (fun p : G × G => conj (k (p.2⁻¹ * p.1))) :=
    Complex.continuous_conj.comp
      (k.continuous.comp (continuous_snd.inv.mul continuous_fst))
  have hfun : pwPhi (G := G) k
      = ⇑(ContinuousMap.toLp 2 (pwHaar G) ℂ) ∘
        ⇑(⟨fun p : G × G => conj (k (p.2⁻¹ * p.1)), hK⟩ : C(G × G, ℂ)).curry := by
    funext g
    simp only [Function.comp_apply]
    change ContinuousMap.toLp 2 (pwHaar G) ℂ _ = _
    congr 1
  rw [hfun]
  exact (ContinuousMap.toLp 2 (pwHaar G) ℂ).continuous.comp
    (⟨fun p : G × G => conj (k (p.2⁻¹ * p.1)), hK⟩ : C(G × G, ℂ)).curry.continuous

/-- Uniform bound on `‖Φ g‖`. -/
theorem pwPhi_bound (k : C(G, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ‖pwPhi (G := G) k g‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (pwPhi_continuous (G := G) k).continuousOn
  exact ⟨‖C‖, norm_nonneg _, fun g => (hC g (Set.mem_univ g)).trans (le_abs_self C)⟩

end PWHelpers
end MathlibExt.Topology.Algebra.PeterWeylWanted
end
