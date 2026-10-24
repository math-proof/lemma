/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Recurrences/SomerLucasInterfaces.lean -/


import sympy.atlas.NumberTheory.Recurrences.LucasSequenceFirstKind
import Lemma.Nat.Recurrences.LucasSequenceFirstKind
import Lemma.Nat.LucasSequence
import sympy.atlas.NumberTheory.Recurrences.NondegenerateLucasPair
import sympy.atlas.NumberTheory.LucasSequence

namespace MetaMathlibExt

example {P Q : ℤ} {u : ℕ → ℤ} (h : IsLucasSequenceFirstKind P Q u) : u 0 = 0 :=
  IsLucasSequenceFirstKind.initialZero h

example {P Q : ℤ} {u : ℕ → ℤ} (h : IsLucasSequenceFirstKind P Q u) : u 1 = 1 :=
  IsLucasSequenceFirstKind.initialOne h

example {P Q : ℤ} {u : ℕ → ℤ} (h : IsLucasSequenceFirstKind P Q u) (n : ℕ) :
    u (n + 2) = P * u (n + 1) - Q * u n :=
  IsLucasSequenceFirstKind.recurrenceStep h n

example {P Q : ℤ} {u : ℕ → ℤ} (h : IsLucasSequenceFirstKind P Q u) : u 2 = P := by
  have h0 := IsLucasSequenceFirstKind.initialZero h
  have h1 := IsLucasSequenceFirstKind.initialOne h
  have h2 := IsLucasSequenceFirstKind.recurrenceStep h 0
  simp only [zero_add] at h2
  rw [h0, h1] at h2
  simpa using h2

example : IsLucasSequenceFirstKind 1 (-1) (lucasU fibonacciLucasParams) := by
  refine ⟨rfl, rfl, fun n => ?_⟩
  simp [lucasU, fibonacciLucasParams]

example {P Q : ℤ} (h : IsNondegenerateLucasPair P Q) : Q ≠ 0 :=
  h.1

example (P : ℤ) : ¬ IsNondegenerateLucasPair P 0 := by
  intro h
  exact h.1 rfl

end MetaMathlibExt
