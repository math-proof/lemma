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
import Def.Topology.Algebra.PeterWeyl.Part2


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
