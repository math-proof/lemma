/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DilcherFiniteMultipleHarmonic.lean -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Rat.Star
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace MetaMathlibExt

noncomputable def dilcherRHS (m n : ℕ) : ℚ :=
  ∑ js ∈ Finset.univ.filter
    (fun js : Fin m → Fin n => Monotone (fun i => (js i).val)),
    (∏ i, ((js i).val + 1 : ℚ))⁻¹

noncomputable def dilcherLHS (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, ((n.choose k : ℚ) * (-1 : ℚ) ^ (k - 1)) / (k : ℚ) ^ m

end MetaMathlibExt
