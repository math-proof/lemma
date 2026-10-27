import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.RingTheory.PiFieldQuotient
open PiFieldQuotient


/--
[eval_zero_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/PiFieldQuotient.lean)
-/
@[path]
private lemma eval_zero_surjective :
  Function.Surjective (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0) := by
  intro y
  exact ⟨Pi.single 0 y, by simp⟩


-- created on 2026-10-23
