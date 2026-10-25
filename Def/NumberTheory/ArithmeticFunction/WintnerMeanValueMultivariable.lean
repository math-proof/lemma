/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/WintnerMeanValueMultivariable.lean -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

open scoped BigOperators Topology

/-! # Multivariable Wintner mean-value theorem
-/

noncomputable def wG (k : ℕ) (f : (Fin k → ℕ) → ℂ) (n : (Fin k → ℕ)) : ℂ :=
  ∑ d : (i : Fin k) → Fin (n i),
    if ∀ i, (d i : ℕ) + 1 ∣ n i then
      (∏ i, (ArithmeticFunction.moebius ((d i : ℕ) + 1) : ℂ)) *
        f (fun i => n i / ((d i : ℕ) + 1))
    else 0

noncomputable def wF (k : ℕ) (f : (Fin k → ℕ) → ℂ) (x m : (Fin k → ℕ)) : ℂ :=
  (wG k f (fun i => m i + 1) * ∏ i, (((x i / (m i + 1) : ℕ)) : ℂ)) / ∏ i, (x i : ℂ)

noncomputable def wBound (k : ℕ) (f : (Fin k → ℕ) → ℂ) (m : (Fin k → ℕ)) : ℝ :=
  ‖wG k f (fun i => m i + 1)‖ / ∏ i, ((m i + 1 : ℕ) : ℝ)

end MetaMathlibExt
end
