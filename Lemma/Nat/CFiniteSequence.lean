import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.CFiniteSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isIntegerCFiniteSequence_of_isSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean)
-/
@[path]
lemma isIntegerCFiniteSequence_of_isSolution
  {E : LinearRecurrence ℤ}
  {s : ℕ → ℤ}
-- given
  (h : E.IsSolution s) :
-- imply
  IsIntegerCFiniteSequence s :=
-- proof
  ⟨E.order, 0, E.coeffs, fun n _ => h n⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isSolution_tail_of_cFiniteWitness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean)
-/
@[path]
lemma isSolution_tail_of_cFiniteWitness
  {s : ℕ → ℤ}
  {p q : ℕ}
  {c : Fin p → ℤ}
-- given
  (h : ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))) :
-- imply
  (LinearRecurrence.mk p c).IsSolution (fun n => s (n + q)) := by
-- proof
  intro n
  have hn : q ≤ n + q := by omega
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (n + q) hn

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsIntegerCFiniteSequence.exists_isSolution_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean)
-/
@[path]
lemma IsIntegerCFiniteSequence.exists_isSolution_tail
  {s : ℕ → ℤ}
-- given
  (h : IsIntegerCFiniteSequence s) :
-- imply
  ∃ (E : LinearRecurrence ℤ) (q : ℕ), E.IsSolution (fun n => s (n + q)) := by
-- proof
  obtain ⟨p, q, c, hc⟩ := h
  exact ⟨LinearRecurrence.mk p c, q, isSolution_tail_of_cFiniteWitness s p q c hc⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
