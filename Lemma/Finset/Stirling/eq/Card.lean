import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.StirlingSecond.eq.NcardParts
open Finset


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  (Stirling n k : ℕ) = ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k).ncard := by
-- proof
  exact StirlingSecond.eq.NcardParts n k


-- created on 2020-10-04
