/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch7Entry1Powersum.lean -/


import Def.Analysis.Ramanujan.Part1Ch7Entry1Powersum
import Lemma.Real.Ramanujan.Part1Ch7Entry1Powersum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry1Powersum

open Asymptotics Filter Topology

open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum

-- For reciprocal square roots, the full one-term expansion has error tending to zero.
example :
    Tendsto
      (fun n : ℕ => chapter7PowerSum ((-1 / 2 : ℝ) : ℂ) n -
        chapter7Entry1Approx ((-1 / 2 : ℝ) : ℂ) 1 n)
      atTop (𝓝 0) := by
  have hO := ramanujan_part1_ch7_entry1_powersum ((-1 / 2 : ℝ) : ℂ) 1
    (by norm_num) (by norm_num) (by norm_num)
  apply hO.trans_tendsto
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  rw [Real.rpow_eq_pow]
  norm_num

-- For the sum of the first n integers, the one-term expansion has error tending to zero.
example :
    Tendsto
      (fun n : ℕ => chapter7PowerSum 1 n - chapter7Entry1Approx 1 1 n)
      atTop (𝓝 0) := by
  have hO := ramanujan_part1_ch7_entry1_powersum (1 : ℂ) 1
    (by norm_num) (by norm_num) (by norm_num)
  apply hO.trans_tendsto
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).comp
    tendsto_natCast_atTop_atTop
  convert h using 1
  funext n
  rw [Real.rpow_eq_pow]
  norm_num

end MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry1Powersum
