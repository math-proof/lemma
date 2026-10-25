/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinomialTMotzkinPaths.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.BinomialTMotzkinPaths


section

open scoped BigOperators

namespace MetaMathlibExt

def baseEquiv (t n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    {p : Fin (n + 1) → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1 + 1),
        0 ≤ ∑ i : Fin (n + 1), if i.1 < m.1 then binomialTMotzkinHeight t (p i) else 0)
        ∧ ∑ i : Fin (n + 1), binomialTMotzkinHeight t (p i) = h}
    ≃ {y : binomialTMotzkinStep t × (Fin n → binomialTMotzkinStep t) //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (y.2 i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (y.2 i) = h - binomialTMotzkinHeight t y.1} :=
  Equiv.subtypeEquiv (Fin.snocEquiv (fun _ => binomialTMotzkinStep t)).symm
    (fun p => pred_iff_symm t n h hh p)

def repackEquiv (t n : ℕ) (h : ℤ) :
    {y : binomialTMotzkinStep t × (Fin n → binomialTMotzkinStep t) //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (y.2 i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (y.2 i) = h - binomialTMotzkinHeight t y.1}
    ≃ Σ s : binomialTMotzkinStep t, {q : Fin n → binomialTMotzkinStep t //
      (∀ m : Fin (n + 1),
        0 ≤ ∑ i : Fin n, if i.1 < m.1 then binomialTMotzkinHeight t (q i) else 0)
        ∧ ∑ i : Fin n, binomialTMotzkinHeight t (q i) = h - binomialTMotzkinHeight t s} where
  toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

noncomputable def binomialTMotzkinDeficitPoly (t N : ℕ) : Polynomial ℚ :=
  (1 + Polynomial.X) ^ (t * N) - Polynomial.C (t : ℚ) * Polynomial.X * (1 + Polynomial.X) ^
      (t * N - 1)

end MetaMathlibExt
end
