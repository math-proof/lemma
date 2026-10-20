import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
open MetaMathlibExt


/--
[peak_generating_function_set_partitions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean)
-/
@[path]
private lemma peak_generating_function_set_partitions_eq
  {k : ℕ}
  {t x q : FractionRing (PowerSeries (Polynomial ℤ))}
-- given
  (hk : 1 ≤ k)
  (hx : x = algebraMap (PowerSeries (Polynomial ℤ)) (FractionRing (PowerSeries (Polynomial ℤ))) PowerSeries.X)
  (hq : q = algebraMap (PowerSeries (Polynomial ℤ)) (FractionRing (PowerSeries (Polynomial ℤ))) (PowerSeries.C Polynomial.X))
  (ht : t = 1 + x ^ 2 * (1 - q) / 2) :
-- imply
  let U : ℤ → FractionRing (PowerSeries (Polynomial ℤ)) := by
-- proof
  apply MetaMathlibExt.peak_generating_function_set_partitions k hk t x q hx hq ht


-- created on 2026-10-20
