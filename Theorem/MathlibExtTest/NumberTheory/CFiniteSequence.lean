/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/CFiniteSequence.lean -/


import Def.NumberTheory.CFiniteSequence
import Lemma.Nat.CFiniteSequence
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

example : IsIntegerCFiniteSequence (fun _ => 0) :=
  ⟨0, 0, Fin.elim0, fun n _ => by simp⟩

example : IsIntegerCFiniteSequence (fun n => if n = 0 then (1 : ℤ) else 0) :=
  ⟨0, 1, Fin.elim0, fun n hn => by
    have hn0 : n ≠ 0 := by
      intro h
      subst h
      simp at hn
    simp [add_zero, hn0]⟩

example : IsIntegerCFiniteSequence (fun _ => (7 : ℤ)) :=
  ⟨1, 0, fun _ => 1, fun n _ => by simp⟩

example : IsIntegerCFiniteSequence (fun _ => (7 : ℤ)) :=
  ⟨2, 0, fun i => (i : ℤ), fun n _ => by
    rw [Fin.sum_univ_two]
    norm_num⟩

example : IsIntegerCFiniteSequence (fun n => (n : ℤ)) :=
  ⟨2, 0, fun i => if i = 0 then -1 else 2, fun n _ => by
    simp [Fin.sum_univ_two]
    ring⟩

example : (LinearRecurrence.mk 1 (fun _ => (2 : ℤ))).IsSolution (fun n => (2 : ℤ) ^ n) := by
  intro n
  simp [pow_succ]
  ring

example : IsIntegerCFiniteSequence (fun n => (2 : ℤ) ^ n) :=
  isIntegerCFiniteSequence_of_isSolution (LinearRecurrence.mk 1 (fun _ => (2 : ℤ))) _ (by
    intro n
    simp [pow_succ]
    ring)

example : (LinearRecurrence.mk 1 (fun _ => (1 : ℤ))).IsSolution (fun _ => (7 : ℤ)) :=
  by
    simpa using
      (isSolution_tail_of_cFiniteWitness (fun _ => (7 : ℤ)) 1 0 (fun _ => 1)
        (fun n _ => by simp))

example :
    (LinearRecurrence.mk 1 (fun _ => (2 : ℤ))).IsSolution
      (fun n => if n + 1 = 0 then 1 else (2 : ℤ) ^ (n + 1)) := by
  let s : ℕ → ℤ := fun n => if n = 0 then 1 else 2 ^ n
  have hs : ∀ n, 1 ≤ n → s (n + 1) = ∑ i : Fin 1, (2 : ℤ) * s (n + (i : ℕ)) := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    simp [s, hn0, pow_succ, mul_comm]
  simpa [s] using isSolution_tail_of_cFiniteWitness s 1 1 (fun _ => 2) hs

end MetaMathlibExt
