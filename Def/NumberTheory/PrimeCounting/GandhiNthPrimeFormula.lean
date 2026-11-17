/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/GandhiNthPrimeFormula.lean -/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

@[expose] public section

open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted

/-- Fiber finset over `m`: pairs `(d, m/d - 1)` for `d ∣ P`, `d ∣ m` (empty if `m = 0`). -/
def gandhiFiber (P m : ℕ) : Finset (↥P.divisors × ℕ) :=
  if m = 0 then ∅
  else ((P.divisors.filter (· ∣ m)).attach.image
    (fun d => ((⟨d.1, (Finset.mem_filter.mp d.2).1⟩, m / d.1 - 1) : ↥P.divisors × ℕ)))

end MathlibExt.NumberTheory.PrimeCounting.GandhiNthPrimeFormulaWanted
