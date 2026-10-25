/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/


import Def.Combinatorics.Enumerative.Partition.PeakGeneratingFunction.Part9
import Lemma.Finset.Enumerative.Partition.PeakGeneratingFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction


namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

open MetaMathlibExt

-- For one block, the peak generating function is `x / (1 - x)`.
example
    (t x q : pgf_testK)
    (hx : x = algebraMap pgf_testR pgf_testK PowerSeries.X)
    (hq : q = algebraMap pgf_testR pgf_testK (PowerSeries.C Polynomial.X))
    (ht : t = 1 + x ^ 2 * (1 - q) / 2) :
    (1 - x) * pgf_testPP1 = x := by
  have h := peak_generating_function_set_partitions 1 (by omega) t x q hx hq ht
  subst x
  subst q
  subst t
  change (1 - pgf_testX) * pgf_testPP1 = pgf_testX
  dsimp only at h
  simp only [pow_one, Finset.Icc_self, Finset.prod_singleton] at h
  norm_num only at h
  simp only [Polynomial.Chebyshev.U_one, Polynomial.Chebyshev.U_zero,
    Polynomial.Chebyshev.U_neg_one, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero, sub_zero, div_one] at h
  have ht : 2 * pgf_testT = 2 + pgf_testX ^ 2 * (1 - pgf_testQ) := by
    unfold pgf_testT
    field_simp [pgf_testTwo_ne_zero]
  unfold pgf_testT pgf_testX pgf_testQ at ht
  rw [ht] at h
  have h' : pgf_testPP1 = pgf_testX * (1 - pgf_testQ) *
      (pgf_testX /
        (pgf_testX * (1 - pgf_testQ) - pgf_testX ^ 2 * (1 - pgf_testQ))) := by
    unfold pgf_testPP1 pgf_testX pgf_testQ
    convert h using 1
    ring
  rw [h']
  calc
    _ = pgf_testX *
        ((pgf_testX * (1 - pgf_testQ) - pgf_testX ^ 2 * (1 - pgf_testQ)) /
          (pgf_testX * (1 - pgf_testQ) - pgf_testX ^ 2 * (1 - pgf_testQ))) := by
      ring
    _ = pgf_testX := by rw [div_self pgf_testDen_ne_zero, mul_one]

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
