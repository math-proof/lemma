/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence
import Theorem.MeasureTheory.Measure.Atomless.Part2


section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-- One greedy Sierpinski step. -/
noncomputable def sierpinskiNext {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (U : SierpinskiState μ s t) :
    SierpinskiState μ s t where
  u := U.u ∪ sierpinskiPiece ht U
  hsub := Set.union_subset U.hsub
    ((sierpinskiPiece_spec ht U).2.1.trans Set.sdiff_subset)
  hmeas := U.hmeas.union (sierpinskiPiece_spec ht U).1
  hle := by
    have hspec := sierpinskiPiece_spec ht U
    have hdisj : Disjoint U.u (sierpinskiPiece ht U) :=
      (Set.disjoint_left.mpr (fun x hx => (hspec.2.1 hx).2)).symm
    rw [measure_union hdisj hspec.1]
    exact hspec.2.2.1

/-- The greedy Sierpinski iteration. -/
noncomputable def sierpinskiSeq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) : ℕ → SierpinskiState μ s t
  | 0 => ⟨∅, Set.empty_subset s, MeasurableSet.empty, by simp⟩
  | n + 1 => sierpinskiNext ht (sierpinskiSeq ht n)

end MeasureTheory
end
