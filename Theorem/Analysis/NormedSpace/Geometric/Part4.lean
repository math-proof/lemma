import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff
import Mathlib.Topology.Separation.CompletelyRegular
import Instance.Analysis.NormedSpace.Geometric.Part2


section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-- The Cantor set continuously surjects onto the (compact metric) dual ball
(Hausdorff–Alexandroff, via `cantorSet ≃ₜ (ℕ → Bool)`). -/
theorem exists_cantor_surjection (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ f : cantorSet → dualBall E, Continuous f ∧ Function.Surjective f := by
  have : Nonempty (dualBall E) := ⟨⟨0, by rw [mem_dualBall]; simp⟩⟩
  have : TopologicalSpace.MetrizableSpace (dualBall E) :=
    WeakDual.metrizable_of_isCompact ℝ E (dualBall E) isCompact_dualBall
  let _inst : MetricSpace (dualBall E) := TopologicalSpace.metrizableSpaceMetric (dualBall E)
  obtain ⟨ψ, hψc, hψs⟩ := exists_nat_bool_continuous_surjective_of_compact (dualBall E)
  exact ⟨ψ ∘ cantorSetHomeomorphNatToBool,
    hψc.comp cantorSetHomeomorphNatToBool.continuous,
    hψs.comp cantorSetHomeomorphNatToBool.surjective⟩

/-! ### Step 3: the linear isometric extension `C(cantorSet, ℝ) →ₗᵢ C([0,1], ℝ)`.

For `f` continuous on the Cantor set, extend it to `[0,1]` by linear interpolation across the
complementary gaps.  `lo y` / `hi y` are the closest Cantor points on either side of `y`. -/

theorem one_mem_cantorSet : (1:ℝ) ∈ cantorSet := by
  rw [cantorSet, mem_iInter]; intro n
  induction n with
  | zero => rw [preCantorSet_zero]; norm_num
  | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩

theorem cantor_subset : cantorSet ⊆ Icc (0:ℝ) 1 := cantorSet_subset_unitInterval

end FunctionalAnalysis.GeometricWanted
end
