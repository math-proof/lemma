import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.Thresholds
open Filter Real SimpleGraph Classical Thresholds


namespace Thresholds

/--
[indicator_exists_le_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/Thresholds.lean)
-/
@[path]
lemma indicator_exists_le_sum
  [Fintype V]
  {n : ℕ}
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {G : SimpleGraph (Fin n)} :
-- imply
  (if ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) ≤ ∑ f : V ↪ Fin n, (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) := by
-- proof
  by_cases h : ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w)
  · rw [if_pos h]
    obtain ⟨f, hf⟩ := h
    have hfterm : (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) = 1 := if_pos hf
    calc (1 : ℝ) = if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then 1 else 0 := hfterm.symm
      _ ≤ ∑ g : V ↪ Fin n, if ∀ v w, H.Adj v w → G.Adj (g v) (g w) then (1 : ℝ) else 0 := by
        apply Finset.single_le_sum _ (Finset.mem_univ f)
        intro i _
        split_ifs <;> linarith
  · rw [if_neg h]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> linarith
/-- The Bernoulli probability that $G$ contains the image of $H$ under a fixed injection
$f : V(H) \hookrightarrow [n]$ is at most $p^{|E(H)|}$, since all $|E(H)|$ edges of $H$
must appear independently. -/

end Thresholds


-- created on 2026-10-23
