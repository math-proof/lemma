/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part38
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarStageStrip_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A) (hW : IsOpen W)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    Topology.IsOpenEmbedding (collarStageStrip g m W hm) := by
  refine ⟨collarStageStrip_isEmbedding g m W hm, ?_⟩
  obtain ⟨O, hOopen, hOW⟩ := isOpen_induced_iff.mp hW
  let V : Set (collarStage g m) :=
    {y | y.val.val.1 ∈ O ∧ y.val.val.2 < 0}
  have hV : IsOpen V :=
    (hOopen.preimage
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val))).inter
      (isOpen_lt
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) continuous_const)
  rw [show range (collarStageStrip g m W hm) = V by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change z.1.val.val ∈ O ∧ z.2.val - 1 < 0
      exact ⟨(Set.ext_iff.mp hOW z.1.val).mpr z.1.property,
        by linarith [z.2.property.2]⟩
    · rintro ⟨hyO, hyneg⟩
      let a : A := ⟨y.val.val.1, collarExternal_fst_mem_of_snd_lt y.val hyneg⟩
      have haW : a ∈ W := by
        exact (Set.ext_iff.mp hOW a).mp hyO
      have hbound : -1 ≤ y.val.val.2 := by
        rcases y.property with hy0 | ⟨ha, ha'⟩
        · exact (ne_of_lt hyneg hy0).elim
        · have haa : (⟨y.val.val.1, ha⟩ : A) = a := by
            apply Subtype.ext
            rfl
          rw [haa, hm a haW] at ha'
          exact ha'
      let t : Set.Ico (0 : ℝ) 1 :=
        ⟨y.val.val.2 + 1, by linarith, by linarith⟩
      let z : W × Set.Ico (0 : ℝ) 1 := (⟨a, haW⟩, t)
      refine ⟨z, ?_⟩
      apply Subtype.ext
      change collarStripMap A (z.1.val, z.2) = y.val
      apply Subtype.ext
      rw [collarStripMap_val]
      apply Prod.ext
      · rfl
      · dsimp [t]
        ring]
  exact hV

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
