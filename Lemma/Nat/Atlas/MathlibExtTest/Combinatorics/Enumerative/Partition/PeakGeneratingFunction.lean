import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
open MathlibExtTest MathlibExtTest.Combinatorics MathlibExtTest.Combinatorics.Enumerative MathlibExtTest.Combinatorics.Enumerative.Partition MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
open MetaMathlibExt


namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

/--
[pgf_testMap_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
lemma pgf_testMap_ne_zero
  {a : pgf_testR}
-- given
  (ha : a ≠ 0) :
-- imply
  algebraMap pgf_testR pgf_testK a ≠ 0 := by
-- proof
  intro haK
  apply ha
  apply IsFractionRing.injective pgf_testR pgf_testK
  simpa using haK

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

/--
[pgf_testDen_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
lemma pgf_testDen_ne_zero :
-- imply
  pgf_testX * (1 - pgf_testQ) - pgf_testX ^ 2 * (1 - pgf_testQ) ≠ 0 := by
-- proof
  have hdenR : (PowerSeries.X * (1 - PowerSeries.C Polynomial.X) -
    PowerSeries.X ^ 2 * (1 - PowerSeries.C Polynomial.X) : pgf_testR) ≠ 0 := by
    intro hd
    have hc := congrArg (PowerSeries.coeff (R := Polynomial ℤ) 1) hd
    have hp := congrArg (fun p : Polynomial ℤ => p.coeff 0) hc
    norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ,
      Finset.Nat.antidiagonal_zero] at hp
  simpa [pgf_testX, pgf_testQ, map_sub, map_mul, map_pow, map_one] using
    pgf_testMap_ne_zero _ hdenR

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

namespace MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction

/--
[pgf_testTwo_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
lemma pgf_testTwo_ne_zero :
-- imply
  (2 : pgf_testK) ≠ 0 := by
-- proof
  have h2R : (2 : pgf_testR) ≠ 0 := by
    intro h2R
    have hc := congrArg PowerSeries.constantCoeff h2R
    rw [map_ofNat, map_zero] at hc
    norm_num at hc
  simpa [map_ofNat] using pgf_testMap_ne_zero (2 : pgf_testR) h2R

end MathlibExtTest.Combinatorics.Enumerative.Partition.PeakGeneratingFunction


-- created on 2026-10-23
-- updated on 2026-10-28
