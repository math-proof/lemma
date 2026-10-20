/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/AlderTotient.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# Alder's totient with second argument fixed at 2

From arXiv:2608.00889v1 `main.tex` lines 294–297: for `k ≥ 1`,
`g(k) = |{ 0 ≤ r < k | gcd(k,r)=gcd(k,2r+1)=1 }|`.
We define `alderTotientTwo k` as the cardinality of `r ∈ Finset.range k`
satisfying `Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)`.
The same formula extends to `k = 0` with `Finset.range 0 = ∅` and value `0`,
as required by `ArithmeticFunction` (`map_zero'`).
-/

namespace ArithmeticFunction

/-- Alder's extension of Euler's totient with second argument `2`.

Counts `r < k` with `gcd(k,r)=1` and `gcd(k,2r+1)=1`.
At `k = 0` the range is empty, with value `0`. -/
def alderTotientTwo : ArithmeticFunction ℕ where
  toFun k :=
    ((Finset.range k).filter fun r =>
      Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)).card
  map_zero' := by simp

@[simp]
theorem alderTotientTwo_apply (k : ℕ) :
    alderTotientTwo k =
      ((Finset.range k).filter fun r =>
        Nat.Coprime k r ∧ Nat.Coprime k (2 * r + 1)).card :=
  rfl

theorem alderTotientTwo_succ_apply (k : ℕ) :
    alderTotientTwo (k + 1) =
      ((Finset.range (k + 1)).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card := by
  have h := alderTotientTwo_apply (k + 1)
  have heq :
      ((Finset.range (k + 1)).filter fun r =>
          Nat.Coprime (k + 1) r ∧ Nat.Coprime (k + 1) (2 * r + 1)) =
        ((Finset.range (k + 1)).filter fun r =>
          Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)) := by
    apply Finset.filter_congr
    intro r _
    exact ⟨fun ⟨h1, h2⟩ => ⟨Nat.coprime_comm.mp h1, Nat.coprime_comm.mp h2⟩,
      fun ⟨h1, h2⟩ => ⟨Nat.coprime_comm.mpr h1, Nat.coprime_comm.mpr h2⟩⟩
  rw [h, heq]

/-- Inclusive `Iic` form of the shifted theorem, matching the source's
`0 ≤ r ≤ k` range: `Finset.Iic k` with source-order predicates. -/
theorem alderTotientTwo_succ_Iic_apply (k : ℕ) :
    alderTotientTwo (k + 1) =
      ((Finset.Iic k).filter fun r =>
        Nat.Coprime r (k + 1) ∧ Nat.Coprime (2 * r + 1) (k + 1)).card := by
  rw [alderTotientTwo_succ_apply]
  congr 1
  ext r
  simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Iic]

theorem alderTotientTwo_zero : alderTotientTwo 0 = 0 :=
  rfl

theorem alderTotientTwo_one : alderTotientTwo 1 = 1 :=
  rfl

/-- Alder's totient is bounded by Euler's totient, by inclusion of filters. -/
theorem alderTotientTwo_le_totient (k : ℕ) :
    alderTotientTwo k ≤ Nat.totient k := by
  rw [alderTotientTwo_apply, Nat.totient_eq_card_coprime k]
  apply Finset.card_le_card
  intro r hr
  simp only [Finset.mem_filter] at hr ⊢
  obtain ⟨hmem, h1, _⟩ := hr
  exact ⟨hmem, h1⟩

end ArithmeticFunction
