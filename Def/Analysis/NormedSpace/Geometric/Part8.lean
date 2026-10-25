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
import Theorem.Analysis.NormedSpace.Geometric.Part8


section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-- The linear isometric extension operator `C(cantorSet, ℝ) →ₗᵢ C([0,1], ℝ)`. -/
noncomputable def extendLI : C(cantorSet, ℝ) →ₗᵢ[ℝ] C(Icc (0:ℝ) 1, ℝ) where
  toFun := gvalCM
  map_add' f g := by
    ext y; simp only [gvalCM_apply, ContinuousMap.add_apply]
    unfold gval; rw [Fext_add, Fext_add]; ring
  map_smul' c f := by
    ext y; simp only [gvalCM_apply, ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    unfold gval; rw [Fext_smul, Fext_smul]; ring
  norm_map' f := by
    change ‖gvalCM f‖ = ‖f‖
    apply le_antisymm
    · rw [ContinuousMap.norm_le _ (norm_nonneg f)]
      intro y
      rw [gvalCM_apply, Real.norm_eq_abs]
      exact gval_abs_le f y.2.1 y.2.2
    · rw [ContinuousMap.norm_le _ (norm_nonneg _)]
      intro s
      calc ‖f s‖ = ‖gvalCM f ⟨s.1, cantor_subset s.2⟩‖ := by
            simp only [gvalCM_apply]; rw [gval_eq s.2 f]
        _ ≤ ‖gvalCM f‖ := ContinuousMap.norm_coe_le_norm _ _

end FunctionalAnalysis.GeometricWanted
end
