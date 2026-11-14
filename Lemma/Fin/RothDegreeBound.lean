import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothDegreeBound_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {P Q : MvPolynomial (Fin m) ℤ} {r s : Fin m → ℕ}
-- given
  (hP : rothDegreeBound P r)
  (hQ : rothDegreeBound Q s) :
-- imply
  rothDegreeBound (P * Q) (fun h ↦ r h + s h) := by
-- proof
  intro i hi h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hi)
  rw [← huv, Finsupp.add_apply]
  apply Nat.add_le_add
  · apply hP u hu
  · apply hQ v hv


-- updated on 2026-11-13
-- created on 2026-10-21
