/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DilcherFiniteMultipleHarmonic.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Star
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.LinearCombination

namespace MetaMathlibExt

private noncomputable def dilcherRHS (m n : ℕ) : ℚ :=
  ∑ js ∈ Finset.univ.filter
    (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
    (∏ i, ((js i).val + 1 : ℚ))⁻¹

private noncomputable def dilcherLHS (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m
end MetaMathlibExt
