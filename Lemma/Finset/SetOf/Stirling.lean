import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset
open Finset


@[main]
private lemma mapping.s2_B
  {n k : ℕ} :
-- imply
  {e | e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e} =
    (fun e : Finset (Finset ℕ) => insert ({n} : Finset ℕ) e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k) := by
-- proof
  exact SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset


-- created on 2026-09-27
