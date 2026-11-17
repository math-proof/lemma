module

public import Mathlib
public import Theorem.Fin.NatAbsCoeff.le.RothMvL1.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvL1.Gt_0.of.Ne_0
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
