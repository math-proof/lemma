/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch7Entry14Bernoullipolymult.lean -/


import Def.Analysis.Ramanujan.Part1Ch7Entry14Bernoullipolymult
import Lemma.Real.Ramanujan.Part1Ch7Entry14Bernoullipolymult


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry14Bernoullipolymult

open Asymptotics Filter

open MathlibExt.Analysis.Ramanujan.Part1Ch7

open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoullipolymult

open scoped Topology

noncomputable section

-- Specialize the theorem's convergence conclusion to `x = 1`.
example (a0 : ℝ) (c : ℕ → ℝ)
    (ha0 : Tendsto chapter7Entry14A0Approx atTop (nhds a0))
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (nhds (c k))) :
    Summable (chapter7Entry14Term 1) :=
  (ramanujan_part1_ch7_entry14_bernoullipolymult a0 c ha0 hc).1 1 zero_lt_one

-- Transfer the sibling normalization at index zero through the bridge.
example (c : ℕ → ℝ) : chapter7StieltjesA c 0 = c 0 := by
  rw [chapter7StieltjesA_eq_entry14Bernoulliasymptotic]
  simp [MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry14Bernoulliasymptotic.chapter7StieltjesA]

-- Transfer the sibling existence and uniqueness theorem through the bridge.
example : ∃! c : ℕ → ℝ,
    (∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (nhds (c k))) ∧
      c 0 = Real.eulerMascheroniConstant := by
  rw [chapter7StieltjesApprox_eq_entry13Bernoullipolyadd]
  exact Entry13Bernoullipolyadd.ramanujan_part1_ch7_entry13_bernoullipolyadd

-- Use summability at `x = 2` to prove that the defining sum is strictly positive.
example : 0 < chapter7Entry14Sum 2 := by
  have hs := summable_chapter7Entry14Term 2 (by norm_num)
  have hterm : ∀ j : ℕ, 0 < chapter7Entry14Term 2 j := by
    intro j
    change 0 < 1 / (((j : ℝ) + 2) * (Real.rpow ((j : ℝ) + 2) 2 - 1))
    have hk : 1 < (j : ℝ) + 2 := by
      have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    exact one_div_pos.mpr (mul_pos (by positivity)
      (sub_pos.mpr (Real.one_lt_rpow hk (by norm_num))))
  unfold chapter7Entry14Sum
  exact hs.tsum_pos (fun j => (hterm j).le) 0 (hterm 0)

end
end MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry14Bernoullipolymult
