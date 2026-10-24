/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Normed/Module/JamesReflexivity.lean -/


import sympy.atlas.Analysis.Normed.Module.JamesReflexivity
import Lemma.Real.Normed.Module.JamesReflexivity
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Operator.NNNorm


namespace MathlibExtTest.Analysis.Normed.Module.JamesReflexivity

open Metric
open MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted

-- Goldstine approximates the identity coordinate of a concrete bidual vector.
example : ∃ x : ℝ, |x| ≤ 1 ∧ |x - (1 / 2 : ℝ)| < 1 / 10 := by
  let T := NormedSpace.inclusionInDoubleDual ℝ ℝ (1 / 2 : ℝ)
  let id : StrongDual ℝ ℝ := ContinuousLinearMap.id ℝ ℝ
  have hT : ‖T‖ ≤ 1 := by
    calc
      ‖T‖ = ‖(1 / 2 : ℝ)‖ :=
        (NormedSpace.inclusionInDoubleDualLi ℝ (E := ℝ)).norm_map _
      _ ≤ 1 := by norm_num
  obtain ⟨x, hx, happrox⟩ := NormedSpace.goldstine_finite T hT {id}
    (by norm_num : (0 : ℝ) < 1 / 10)
  refine ⟨x, ?_, ?_⟩
  · simpa [Real.norm_eq_abs] using hx
  · simpa [id, T, NormedSpace.dual_def] using happrox id (by simp)

-- James' theorem proves reflexivity of the Euclidean plane from compact norm attainment.
example : Function.Surjective
    (NormedSpace.inclusionInDoubleDual ℝ (EuclideanSpace ℝ (Fin 2))) := by
  rw [james_reflexivity]
  intro f
  obtain ⟨x, hx, hmax⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).exists_isMaxOn
      (nonempty_closedBall.mpr zero_le_one) f.continuous.norm.continuousOn
  refine ⟨x, hx, le_antisymm ?_ ?_⟩
  · exact (f.le_opNorm x).trans
      (mul_le_of_le_one_right (norm_nonneg f) (mem_closedBall_zero_iff.mp hx))
  · by_contra h
    have hlt : ‖f x‖ < ‖f‖ := lt_of_not_ge h
    obtain ⟨y, hy, hfy⟩ := f.exists_lt_apply_of_lt_opNorm hlt
    exact (not_lt_of_ge (hmax (mem_closedBall_zero_iff.mpr hy.le))) hfy

end MathlibExtTest.Analysis.Normed.Module.JamesReflexivity
