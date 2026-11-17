module

public import Mathlib
public import Theorem.Fin.RothMvL1Add.le.AddRothSMvL1
public import Theorem.Fin.RothMvL1Neg.eq.RothMvL1

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvL1_Sub.le.AddRothSMvL1
  {m : ℕ}
  (P Q : MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 (P - Q) ≤ rothMvL1 P + rothMvL1 Q := by
-- proof
  rw [sub_eq_add_neg]
  simpa [RothMvL1Neg.eq.RothMvL1] using RothMvL1Add.le.AddRothSMvL1 P (-Q)


-- created on 2026-10-21
