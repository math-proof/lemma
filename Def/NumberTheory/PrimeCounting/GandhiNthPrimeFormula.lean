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
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted

/-- Fiber finset over `m`: pairs `(d, m/d - 1)` for `d ∣ P`, `d ∣ m` (empty if `m = 0`). -/
def gandhiFiber (P m : ℕ) : Finset (↥P.divisors × ℕ) :=
  if m = 0 then ∅
  else ((P.divisors.filter (· ∣ m)).attach.image
    (fun d => ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩, m / d.1 - 1) : ↥P.divisors × ℕ)))

end MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted
