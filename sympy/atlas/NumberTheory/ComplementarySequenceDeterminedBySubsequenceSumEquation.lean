/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ComplementarySequenceDeterminedBySubsequenceSumEquation.lean -/

import Mathlib.Order.Monotone.Basic

/-!
Complementary sequences determined by subsequence-sum equations.

Concept `jis_sem_c59328d30afb85fa4bde030d`
(canonical name: complementary sequence determined by subsequence-sum equation).
Source statements `jis_a728ee017c7adb1e5151b44f`, `jis_d5c85a6cd10b01207e0aa227`,
`jis_f769f4ddb64ff3cef3f34a43` are definition context only; the surrounding
conjecture/theorem conclusions (linear recurrences, closed forms) are excluded.
-/

namespace MetaMathlibExt

/-- Strictly increasing complementary sequences partitioning the positive naturals
(concept `jis_sem_c59328d30afb85fa4bde030d`; statements `jis_a728ee017c7adb1e5151b44f`,
`jis_d5c85a6cd10b01207e0aa227`, `jis_f769f4ddb64ff3cef3f34a43`). -/
def IsComplementaryPair (a b : ℕ → ℕ) : Prop :=
  (∀ n, 0 < a n) ∧ (∀ n, 0 < b n) ∧
    StrictMono a ∧ StrictMono b ∧
    (∀ m n, a m ≠ b n) ∧
    ∀ n, 0 < n → (∃ m, a m = n) ∨ (∃ m, b m = n)

/-- Parametrized subsequence-sum equation `a_n = b_{hn} + b_{khn}` with `2 ≤ h`,
`2 ≤ k` and `b_0 = 1` (concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_a728ee017c7adb1e5151b44f`). -/
def SatisfiesParametrizedSumEquation (a b : ℕ → ℕ) (h k : ℕ) : Prop :=
  2 ≤ h ∧ 2 ≤ k ∧ b 0 = 1 ∧ ∀ n, a n = b (h * n) + b (k * h * n)

/-- Base equation `a_n = b_{2n} + b_{4n}` with `b_0 = 1`
(concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_d5c85a6cd10b01207e0aa227`). -/
def SatisfiesBaseSumEquation (a b : ℕ → ℕ) : Prop :=
  b 0 = 1 ∧ ∀ n, a n = b (2 * n) + b (4 * n)

/-- Shifted equation `a_n = b_{2n} + b_{4n} + 1` with `b_0 = 1`
(concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_f769f4ddb64ff3cef3f34a43`). -/
def SatisfiesShiftedSumEquation (a b : ℕ → ℕ) : Prop :=
  b 0 = 1 ∧ ∀ n, a n = b (2 * n) + b (4 * n) + 1

/-- Complementary pair determined by the parametrized equation
(concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_a728ee017c7adb1e5151b44f`). -/
def IsComplementaryDeterminedByParametrizedSumEquation
    (a b : ℕ → ℕ) (h k : ℕ) : Prop :=
  IsComplementaryPair a b ∧ SatisfiesParametrizedSumEquation a b h k

/-- Complementary pair determined by the base equation
(concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_d5c85a6cd10b01207e0aa227`). -/
def IsComplementaryDeterminedByBaseSumEquation (a b : ℕ → ℕ) : Prop :=
  IsComplementaryPair a b ∧ SatisfiesBaseSumEquation a b

/-- Complementary pair determined by the shifted equation
(concept `jis_sem_c59328d30afb85fa4bde030d`;
statement `jis_f769f4ddb64ff3cef3f34a43`). -/
def IsComplementaryDeterminedByShiftedSumEquation (a b : ℕ → ℕ) : Prop :=
  IsComplementaryPair a b ∧ SatisfiesShiftedSumEquation a b

end MetaMathlibExt
