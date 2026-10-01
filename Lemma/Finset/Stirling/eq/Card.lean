import sympy.sets.stirling_partition
import sympy.Basic
open Finset


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  (Stirling n k : ℕ) = ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k).ncard := by
-- proof
  exact Stirling.conditionset.stirlingSecond_eq_ncard n k


-- created on 2026-09-27
