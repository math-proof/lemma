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
import Theorem.Analysis.NormedSpace.Geometric.Part3


section

open Set

namespace FunctionalAnalysis.GeometricWanted

/-- The canonical linear isometric embedding `E →ₗᵢ C(B_{E*}, ℝ)`. -/
noncomputable def toCK {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    E →ₗᵢ[ℝ] C(dualBall E, ℝ) where
  toFun := evalCM
  map_add' x y := by ext φ; simp [map_add]
  map_smul' c x := by ext φ; simp [map_smul]
  norm_map' x := by
    change ‖evalCM x‖ = ‖x‖
    apply le_antisymm
    · rw [ContinuousMap.norm_le _ (norm_nonneg x)]
      intro φ
      rw [evalCM_apply]
      calc ‖(φ : WeakDual ℝ E) x‖
          = ‖(WeakDual.toStrongDual (φ : WeakDual ℝ E)) x‖ := by rw [WeakDual.toStrongDual_apply]
        _ ≤ ‖WeakDual.toStrongDual (φ : WeakDual ℝ E)‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ x
        _ ≤ 1 * ‖x‖ := by gcongr; exact (mem_dualBall.mp φ.2)
        _ = ‖x‖ := one_mul _
    · obtain ⟨g, hg1, hgx⟩ := exists_dual_vector'' ℝ x
      have hmem : StrongDual.toWeakDual g ∈ dualBall E := by
        rw [mem_dualBall]; simpa using hg1
      calc ‖x‖ = |g x| := by rw [hgx]; exact (abs_of_nonneg (norm_nonneg x)).symm
        _ = ‖evalCM x ⟨StrongDual.toWeakDual g, hmem⟩‖ := by
              rw [evalCM_apply, Real.norm_eq_abs]; rfl
        _ ≤ ‖evalCM x‖ := ContinuousMap.norm_coe_le_norm _ _

/-! ### Precomposition by a continuous surjection is a linear isometry. -/

def precompLI {α β : Type*} [TopologicalSpace α] [CompactSpace α]
    [TopologicalSpace β] [CompactSpace β] (g : C(α, β)) (hg : Function.Surjective g) :
    C(β, ℝ) →ₗᵢ[ℝ] C(α, ℝ) where
  toFun f := f.comp g
  map_add' f₁ f₂ := by ext a; simp
  map_smul' c f := by ext a; simp
  norm_map' f := by
    apply le_antisymm
    · rw [ContinuousMap.norm_le _ (norm_nonneg f)]
      intro a
      simpa using ContinuousMap.norm_coe_le_norm f (g a)
    · rw [ContinuousMap.norm_le _ (norm_nonneg _)]
      intro b
      obtain ⟨a, rfl⟩ := hg b
      simpa using ContinuousMap.norm_coe_le_norm (f.comp g) a

end FunctionalAnalysis.GeometricWanted
end
