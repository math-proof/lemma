/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Instance.Analysis.NormedSpace.LocalReflexivity


namespace FunctionalAnalysis.LocalReflexivityWanted

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable section

/-- The norm of a scalar is the real part of its product with some unit scalar. -/
theorem plr_exists_unit_mul (c : 𝕜) :
    ∃ u : 𝕜, ‖u‖ = 1 ∧ RCLike.re (u * c) = ‖c‖ := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, norm_one, by simp⟩
  · have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hne : ‖c‖ ≠ 0 := ne_of_gt hpos
    refine ⟨(↑(‖c‖⁻¹) : 𝕜) * starRingEnd 𝕜 c, ?_, ?_⟩
    · rw [norm_mul, RCLike.norm_ofReal, RCLike.norm_conj,
        abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hne]
    · have hcc : starRingEnd 𝕜 c * c = (↑‖c‖ : 𝕜) ^ 2 := by
        rw [mul_comm]
        exact RCLike.mul_conj c
      have hreal : ‖c‖⁻¹ * ‖c‖ ^ 2 = ‖c‖ := by
        rw [sq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
      have hmul2 : (↑(‖c‖⁻¹) : 𝕜) * ((↑‖c‖ : 𝕜) ^ 2) = (↑‖c‖ : 𝕜) := by
        have h : (↑(‖c‖⁻¹ * ‖c‖ ^ 2) : 𝕜) = (↑‖c‖ : 𝕜) := by rw [hreal]
        rw [← RCLike.ofReal_pow, ← RCLike.ofReal_mul, h]
      rw [mul_assoc, hcc, hmul2, RCLike.ofReal_re]

/-- The canonical embedding into the double dual is injective. -/
theorem plr_J_inj {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    Function.Injective (NormedSpace.inclusionInDoubleDual 𝕜 E) := by
  intro x y h
  apply (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).injective
  change (NormedSpace.inclusionInDoubleDual 𝕜 E) x =
    (NormedSpace.inclusionInDoubleDual 𝕜 E) y
  exact h

end
end FunctionalAnalysis.LocalReflexivityWanted
