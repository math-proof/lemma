import Mathlib
import Initialize.Tactic.Attr.Basic


namespace Real_Analysis

/--
[cauchy_seq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Cauchy.lean)
-/
@[path]
lemma cauchy_seq_iff
  {x : ℕ → ℝ} :
-- imply
  CauchySeq x ↔ ∀ ε > 0, ∃ M : ℕ, ∀ n k, n ≥ M → k ≥ M → := by
-- proof
  rw [Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n k hn hk => by rw [← Real.dist_eq]; exact hN n hn k hk⟩
  · intro h ε hε
    obtain ⟨M, hM⟩ := h ε hε
    exact ⟨M, fun m hm n hn => by rw [Real.dist_eq]; exact hM m n hm hn⟩

end Real_Analysis

namespace Real_Analysis

/--
[cauchy_iff_convergent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Cauchy.lean)
-/
@[path]
lemma cauchy_iff_convergent
  {x : ℕ → ℝ} :
-- imply
  CauchySeq x ↔ ∃ L : ℝ, Filter.Tendsto x Filter.atTop (nhds L) := by
-- proof
  constructor
  · exact cauchySeq_tendsto_of_complete
  · rintro ⟨L, hL⟩
    exact hL.cauchySeq

end Real_Analysis


-- created on 2026-10-23
