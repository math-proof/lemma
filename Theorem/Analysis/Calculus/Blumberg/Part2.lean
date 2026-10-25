import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Def.Analysis.Calculus.Blumberg


section

namespace MetaMathlibExt

-- N2a: catPts is closed.
theorem blum_isClosed_cat (A : Set ℝ) : IsClosed (blumCat A) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ IsMeagre (A ∩ U) := by
    by_contra h
    apply hx
    intro U hUo hxU hCon
    exact h ⟨U, hUo, hxU, hCon⟩
  obtain ⟨U, hUo, hxU, hUm⟩ := hx'
  refine ⟨U, ?_, hUo, hxU⟩
  intro y hy hyC
  exact hyC U hUo hy hUm

-- N2b: A minus its category points is meagre.
theorem blum_diff_cat_isMeagre (A : Set ℝ) : IsMeagre (A \ blumCat A) := by
  set T : Set (ℚ × ℚ) := {pq | IsMeagre (A ∩ Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ))} with hT
  have hTcount : T.Countable := Set.to_countable T
  have hsub : A \ blumCat A ⊆ ⋃ pq ∈ T, (A ∩ Set.Ioo (pq.1 : ℝ) (pq.2 : ℝ)) := by
    intro x hx
    obtain ⟨hxA, hxC⟩ : x ∈ A ∧ x ∉ blumCat A := hx
    have hx' : ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ IsMeagre (A ∩ U) := by
      by_contra h
      apply hxC
      intro U hUo hxU hCon
      exact h ⟨U, hUo, hxU, hCon⟩
    obtain ⟨U, hUo, hxU, hUm⟩ := hx'
    obtain ⟨V, hVb, hxV, hVU⟩ :=
      Real.isTopologicalBasis_Ioo_rat.exists_subset_of_mem_open hxU hUo
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hVb
    obtain ⟨p, q, -, rfl⟩ := hVb
    have hmono : A ∩ Set.Ioo (↑p : ℝ) (↑q : ℝ) ⊆ A ∩ U := by
      intro y hy
      exact ⟨hy.1, hVU hy.2⟩
    have hpqT : (p, q) ∈ T := IsMeagre.mono hmono hUm
    exact Set.mem_biUnion hpqT ⟨hxA, hxV⟩
  apply IsMeagre.mono hsub
  apply isMeagre_biUnion hTcount
  intro pq hpq
  have : pq ∈ T := hpq
  simpa [hT] using this

-- N3: A minus the interior of its category points is meagre.
theorem blum_diff_interior_cat_isMeagre (A : Set ℝ) :
    IsMeagre (A \ interior (blumCat A)) := by
  have hC := blum_isClosed_cat A
  have hfront : IsMeagre (frontier (blumCat A)) := by
    apply IsNowhereDense.isMeagre
    rw [IsClosed.isNowhereDense_iff isClosed_frontier]
    exact interior_frontier hC
  have hsub : A \ interior (blumCat A) ⊆
      (A \ blumCat A) ∪ frontier (blumCat A) := by
    intro x hx
    obtain ⟨hxA, hxin⟩ : x ∈ A ∧ x ∉ interior (blumCat A) := hx
    by_cases hxC : x ∈ blumCat A
    · right
      have hmem : x ∈ blumCat A \ interior (blumCat A) := ⟨hxC, hxin⟩
      rwa [← hC.frontier_eq] at hmem
    · left
      exact ⟨hxA, hxC⟩
  exact IsMeagre.mono hsub (IsMeagre.union (blum_diff_cat_isMeagre A) hfront)

end MetaMathlibExt
end
