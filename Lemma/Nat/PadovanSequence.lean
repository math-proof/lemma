import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PadovanSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[shiftedPadovanSequence_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PadovanSequence.lean)
-/
@[path]
lemma shiftedPadovanSequence_add_three
  {n : Nat} :
-- imply
  shiftedPadovanSequence (n + 3) =
      shiftedPadovanSequence (n + 1) + shiftedPadovanSequence n :=
-- proof
  rfl

end MetaMathlibExt

/--
[shiftedPadovanSequence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PadovanSequence.lean)
-/
@[path]
private lemma shiftedPadovanSequence_zero_eq
  :
-- imply
  shiftedPadovanSequence 0 = 1 := by
-- proof
  apply MetaMathlibExt.shiftedPadovanSequence_zero

/--
[shiftedPadovanSequence_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PadovanSequence.lean)
-/
@[path]
private lemma shiftedPadovanSequence_one_eq
  :
-- imply
  shiftedPadovanSequence 1 = 0 := by
-- proof
  apply MetaMathlibExt.shiftedPadovanSequence_one

/--
[shiftedPadovanSequence_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PadovanSequence.lean)
-/
@[path]
private lemma shiftedPadovanSequence_two_eq
  :
-- imply
  shiftedPadovanSequence 2 = 1 := by
-- proof
  apply MetaMathlibExt.shiftedPadovanSequence_two


-- created on 2026-10-20
-- updated on 2026-10-23
