/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/GandhiNthPrimeFormula.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorem.NumberTheory.PrimeCounting.GandhiNthPrimeFormula
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted

/-- The equivalence between the sigma of fibers and the product. -/
def gandhiEquiv (P : ℕ) : (Σ m : ℕ, ↥(gandhiFiber P m)) ≃ (↥P.divisors × ℕ) where
  toFun q := q.2.1
  invFun p := ⟨p.1.1 * (p.2 + 1), ⟨p, gandhiFiber_self_mem P p⟩⟩
  left_inv := by
    rintro ⟨m, p, hpm⟩
    rcases eq_or_ne m 0 with rfl | hm
    · have hS : gandhiFiber P 0 = ∅ := by simp [gandhiFiber]
      rw [hS] at hpm
      exact (Finset.notMem_empty p hpm).elim
    · have hFm : p.1.1 * (p.2 + 1) = m := gandhiFiber_proj P m hm p hpm
      subst hFm
      rfl
  right_inv := fun p => rfl

end MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted
