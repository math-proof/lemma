/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/WintnerMeanValueMultivariable.lean -/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

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
