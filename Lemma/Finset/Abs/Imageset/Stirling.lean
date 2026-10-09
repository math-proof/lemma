import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.NcardImageConditionset.eq.NcardImageImageConditionset
open Finset


@[path]
private lemma mapping.s0_B
  {n k : ℕ} :
-- imply
  ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k).ncard =
    ((fun e : Finset (Finset ℕ) => insert ({n} : Finset ℕ) e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k)).ncard := by
-- proof
  exact NcardImageConditionset.eq.NcardImageImageConditionset


-- created on 2026-09-27
