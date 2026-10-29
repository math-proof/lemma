import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Analysis.Complex.NormalConvergence
open Complex MeasureTheory Topology Set Filter N329Test


namespace N329Test

/--
[complexOneTermSeries_differentiableOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma complexOneTermSeries_differentiableOn
  {n : Nat} :
-- imply
  DifferentiableOn Complex (complexOneTermSeries n) Set.univ := by
-- proof
  by_cases hn : n = 0
  · subst hn
    have hfun : complexOneTermSeries 0 = fun _ => 1 := by
      funext z
      simp [complexOneTermSeries]
    rw [hfun]
    exact differentiableOn_const 1
  · have hfun : complexOneTermSeries n = fun _ => 0 := by
    funext z
    simp [complexOneTermSeries, hn]
    rw [hfun]
    exact differentiableOn_const 0

end N329Test

/--
[complexOneTermSeries_supNormOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma complexOneTermSeries_supNormOn
  {n : Nat} :
-- imply
  supNormOn (complexOneTermSeries n) (Set.univ : Set Complex) = if n = 0 then (1 : ENNReal) else 0 := by
-- proof
  have : Nonempty ↥((Set.univ : Set Complex)) := ⟨⟨0, Set.mem_univ _⟩⟩
  unfold supNormOn
  by_cases hn : n = 0
  · subst hn
    rw [ite_eq_left rfl]
    have hbody : ∀ x : ↥((Set.univ : Set Complex)),
      ENNReal.ofReal ‖complexOneTermSeries 0 x‖ = 1 := by
      intro x
      simp [complexOneTermSeries]
    simp only [hbody]
    exact iSup_const
  · rw [ite_eq_right hn]
    have hbody : ∀ x : ↥((Set.univ : Set Complex)),
      ENNReal.ofReal ‖complexOneTermSeries n x‖ = 0 := by
      intro x
      simp [complexOneTermSeries, hn]
    simp only [hbody]
    exact iSup_const


namespace N329Test

/--
[complexOneTermSeries_convergesNormallyOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma complexOneTermSeries_convergesNormallyOn :
-- imply
  ConvergesNormallyOn complexOneTermSeries Set.univ := by
-- proof
  unfold ConvergesNormallyOn
  rw [tsum_congr complexOneTermSeries_supNormOn,
    tsum_eq_single 0 (fun b hb => ite_eq_right hb), ite_eq_left rfl]
  exact ENNReal.one_ne_top

end N329Test

namespace N329Test

/--
[complexOneTermSeries_convergesLocallyNormallyOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Complex/NormalConvergence.lean)
-/
@[path]
lemma complexOneTermSeries_convergesLocallyNormallyOn :
-- imply
  ConvergesLocallyNormallyOn complexOneTermSeries Set.univ := by
-- proof
  intro z _
  exact ⟨Set.univ, Filter.univ_mem, by simpa using
    complexOneTermSeries_convergesNormallyOn⟩

end N329Test


-- created on 2026-10-23
-- updated on 2026-10-28
