/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch7Entry14Bernoulliasymptotic.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
import Lemma.Real.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic

namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic

open Filter Topology MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoulliasymptotic

-- The theorem specializes its identity to `s = 1`.
example (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
    (∑' j : ℕ, chapter7Entry14Cor2LeftTerm 1 j) =
      -Real.log 1 + chapter7Entry14Cor2Constant c +
        (1 - Real.eulerMascheroniConstant) * 1 -
          ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c 1 j :=
  ((ramanujan_part1_ch7_entry14_bernoulliasymptotic c hc).2.2 1 one_pos).2.2

-- Positive `s` gives a summable power series.
example (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (s : ℝ) (hs : 0 < s) : Summable (chapter7Entry14Cor2PowerTerm c s) :=
  ((ramanujan_part1_ch7_entry14_bernoulliasymptotic c hc).2.2 s hs).2.1

end MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry14Bernoulliasymptotic
