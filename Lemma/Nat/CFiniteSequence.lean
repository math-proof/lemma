import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CFiniteSequence
open MetaMathlibExt


/--
[isIntegerCFiniteSequence_of_isSolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean)
-/
@[path]
private lemma isIntegerCFiniteSequence_of_isSolution_eq
  {E : LinearRecurrence ℤ}
  {s : ℕ → ℤ}
-- given
  (h : E.IsSolution s) :
-- imply
  IsIntegerCFiniteSequence s := by
-- proof
  apply MetaMathlibExt.isIntegerCFiniteSequence_of_isSolution E s h

/--
[isSolution_tail_of_cFiniteWitness](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean)
-/
@[path]
private lemma isSolution_tail_of_cFiniteWitness_eq
  {s : ℕ → ℤ}
  {p q : ℕ}
  {c : Fin p → ℤ}
-- given
  (h : ∀ n, q ≤ n → s (n + p) = ∑ i, c i * s (n + (i : ℕ))) :
-- imply
  (LinearRecurrence.mk p c).IsSolution (fun n => s (n + q)) := by
-- proof
  apply MetaMathlibExt.isSolution_tail_of_cFiniteWitness s p q c h

/--
[IsIntegerCFiniteSequence.exists_isSolution_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CFiniteSequence.lean)
-/
@[path]
private lemma IsIntegerCFiniteSequence_exists_isSolution_tail_eq
  {s : ℕ → ℤ}
-- given
  (h : IsIntegerCFiniteSequence s) :
-- imply
  ∃ (E : LinearRecurrence ℤ) (q : ℕ), E.IsSolution (fun n => s (n + q)) := by
-- proof
  apply MetaMathlibExt.IsIntegerCFiniteSequence.exists_isSolution_tail h


-- created on 2026-10-20
