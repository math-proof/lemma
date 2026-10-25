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
import Def.Analysis.Calculus.Blumberg.Part2


section

namespace MetaMathlibExt

-- N4: the bad points form a meagre set.
theorem blum_isMeagre_not_good (f : ℝ → ℝ) :
    IsMeagre {x | ¬ blumGood f x} := by
  have hmeag : IsMeagre (⋃ k : ℕ, ⋃ q : ℚ,
      ({y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} \
        interior (blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))}))) :=
    isMeagre_iUnion fun k => isMeagre_iUnion fun q =>
      blum_diff_interior_cat_isMeagre _
  apply IsMeagre.mono _ hmeag
  intro x hx
  have hxG : ¬ blumGood f x := hx
  obtain ⟨ε, hεpos, hεfail⟩ : ∃ ε : ℝ, ε > 0 ∧ ∀ δ : ℝ, δ > 0 →
      ∃ V : Set ℝ, IsOpen V ∧ V.Nonempty ∧ V ⊆ Metric.ball x δ ∧
        IsMeagre ({y | dist (f y) (f x) < ε} ∩ V) := by
    by_contra h
    apply hxG
    intro ε' hε'
    by_contra hδ
    apply h
    refine ⟨ε', hε', ?_⟩
    intro δ hδ'
    by_contra hV
    apply hδ
    refine ⟨δ, hδ', ?_⟩
    intro V hVo hVne hVsub
    by_contra hCon
    exact hV ⟨V, hVo, hVne, hVsub, hCon⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hεpos
  have hKpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hfail0 : ∀ δ : ℝ, δ > 0 → ∃ V : Set ℝ, IsOpen V ∧ V.Nonempty ∧
      V ⊆ Metric.ball x δ ∧
      IsMeagre ({y | dist (f y) (f x) < 1 / ((k : ℝ) + 1)} ∩ V) := by
    intro δ hδ
    obtain ⟨V, hVo, hVne, hVsub, hVm⟩ := hεfail δ hδ
    refine ⟨V, hVo, hVne, hVsub, ?_⟩
    apply IsMeagre.mono _ hVm
    intro y hy
    obtain ⟨hy1, hy2⟩ :
      dist (f y) (f x) < 1 / ((k : ℝ) + 1) ∧ y ∈ V := hy
    refine ⟨?_, hy2⟩
    change dist (f y) (f x) < ε
    exact lt_of_lt_of_le hy1 (le_of_lt hk)
  have hrpos : (0 : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by
    apply one_div_pos.mpr
    linarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show (f x - 1 / (2 * ((k : ℝ) + 1))) < (f x + 1 / (2 * ((k : ℝ) + 1))) by
      linarith)
  have hdist : dist (f x) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hBsub : {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} ⊆
      {y | dist (f y) (f x) < 1 / ((k : ℝ) + 1)} := by
    intro y hy
    have hy' : dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1)) := hy
    change dist (f y) (f x) < 1 / ((k : ℝ) + 1)
    have hKne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hKpos
    have htri := dist_triangle (f y) (q : ℝ) (f x)
    have hqc : dist (q : ℝ) (f x) = dist (f x) (q : ℝ) := dist_comm _ _
    have h2 : (1 : ℝ) / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) =
        1 / ((k : ℝ) + 1) := by
      field_simp
      ring
    calc dist (f y) (f x)
        ≤ dist (f y) (q : ℝ) + dist (q : ℝ) (f x) := htri
      _ = dist (f y) (q : ℝ) + dist (f x) (q : ℝ) := by rw [hqc]
      _ < 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) :=
          add_lt_add hy' hdist
      _ = 1 / ((k : ℝ) + 1) := h2
  have hxB : x ∈ {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} := hdist
  have hxNI : x ∉ interior
      (blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))}) := by
    intro hxin
    obtain ⟨δ', hδ'pos, hδ'sub⟩ :=
      Metric.isOpen_iff.mp isOpen_interior x hxin
    have hsub2 : Metric.ball x δ' ⊆
        blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} :=
      fun y hy => interior_subset (hδ'sub hy)
    obtain ⟨V, hVo, hVne, hVsub, hVm⟩ := hfail0 δ' hδ'pos
    obtain ⟨z, hzV⟩ := hVne
    have hzC : z ∈
        blumCat {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} :=
      hsub2 (hVsub hzV)
    have hzNC : ¬ IsMeagre
        ({y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} ∩ V) :=
      hzC V hVo hzV
    apply hzNC
    apply IsMeagre.mono _ hVm
    intro y hy
    obtain ⟨hy1, hy2⟩ :
      y ∈ {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} ∧ y ∈ V := hy
    exact ⟨hBsub hy1, hy2⟩
  have hmem : x ∈ {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))} \
      interior (blumCat
        {y | dist (f y) (q : ℝ) < 1 / (2 * ((k : ℝ) + 1))}) := ⟨hxB, hxNI⟩
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨q, hmem⟩⟩

end MetaMathlibExt
end
