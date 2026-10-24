/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/


import sympy.atlas.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
import Lemma.Finset.Enumerative.Partition.PeakGeneratingFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring


namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

open MetaMathlibExt

abbrev pgf_testR := PowerSeries (Polynomial ℤ)
abbrev pgf_testK := FractionRing pgf_testR

noncomputable def pgf_testX : pgf_testK :=
  algebraMap pgf_testR pgf_testK PowerSeries.X

noncomputable def pgf_testQ : pgf_testK :=
  algebraMap pgf_testR pgf_testK (PowerSeries.C Polynomial.X)

noncomputable def pgf_testT : pgf_testK :=
  1 + pgf_testX ^ 2 * (1 - pgf_testQ) / 2

noncomputable def pgf_testPP1 : pgf_testK :=
  algebraMap pgf_testR pgf_testK (PowerSeries.mk (fun n => ∑ w ∈ Finset.univ.filter
    (fun w : Fin n → Fin 1 => IsSurjectiveRestrictedGrowthString w),
    Polynomial.X ^ (Finset.filter
      (fun s : Fin n × Fin n × Fin n =>
        s.1.val + 1 = s.2.1.val ∧ s.2.1.val + 1 = s.2.2.val ∧
        w s.1 < w s.2.1 ∧ w s.2.2 < w s.2.1) Finset.univ).card))

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
