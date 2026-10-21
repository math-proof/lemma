import Mathlib
import Lemma.Fin.NatAbsCoeff.le.RothMvL1.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {P : MvPolynomial (Fin m) ℤ}
-- given
  (hP : P ≠ 0) :
-- imply
  0 < rothMvL1 P := by
-- proof
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hP
  exact (Int.natAbs_pos.mpr (MvPolynomial.mem_support_iff.mp hi)).trans_le
    (NatAbsCoeff.le.RothMvL1.of.RothMvIndex P i)


-- created on 2026-10-21
