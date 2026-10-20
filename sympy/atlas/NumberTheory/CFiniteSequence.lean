/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean -/

import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic.Order

namespace MetaMathlibExt

/-- An integer sequence is C-finite if it eventually satisfies a fixed
constant-coefficient linear recurrence.

Concept `jis_term_8dfeefcfa70ce96efa8b4fb3`; source JIS VOL26/Fischer–Kotek–Makowsky,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Makowsky/makowsky16.tex>, lines 249–259. -/
def IsIntegerCFiniteSequence (s : ℕ → ℤ) : Prop :=
  ∃ p q, ∃ c : Fin p → ℤ, ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))

/-- Every solution of a `LinearRecurrence` is C-finite. -/
theorem isIntegerCFiniteSequence_of_isSolution (E : LinearRecurrence ℤ) (s : ℕ → ℤ)
    (h : E.IsSolution s) : IsIntegerCFiniteSequence s :=
  ⟨E.order, 0, E.coeffs, fun n _ => h n⟩

/-- An eventual C-finite recurrence becomes a `LinearRecurrence` solution after
discarding the finite exceptional prefix. -/
theorem isSolution_tail_of_cFiniteWitness (s : ℕ → ℤ) (p q : ℕ) (c : Fin p → ℤ)
    (h : ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))) :
    (LinearRecurrence.mk p c).IsSolution (fun n => s (n + q)) := by
  intro n
  have hn : q ≤ n + q := by omega
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (n + q) hn

/-- A C-finite sequence has a tail that is a solution of a `LinearRecurrence`. -/
theorem IsIntegerCFiniteSequence.exists_isSolution_tail {s : ℕ → ℤ}
    (h : IsIntegerCFiniteSequence s) :
    ∃ (E : LinearRecurrence ℤ) (q : ℕ), E.IsSolution (fun n => s (n + q)) := by
  obtain ⟨p, q, c, hc⟩ := h
  exact ⟨LinearRecurrence.mk p c, q, isSolution_tail_of_cFiniteWitness s p q c hc⟩

end MetaMathlibExt
