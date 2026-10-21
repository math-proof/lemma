import Mathlib
import Lemma.Fin.RothMvL1Det.le.MulFactorialPow.of.All_LeRothMvL1
import Lemma.Fin.RothMvL1_RothMvHasse.le.MulPow2SumRothMvL1.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothHasseDet_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k : ℕ}
-- given
  (P : MvPolynomial (Fin m) ℤ)
  (r : Fin m → ℕ)
  (hP : rothDegreeBound P r)
  (u v : Fin k → RothMvIndex m) :
-- imply
  rothMvL1 (rothHasseDet P u v) ≤
    k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k := by
-- proof
  apply RothMvL1Det.le.MulFactorialPow.of.All_LeRothMvL1
  intro s t
  exact RothMvL1_RothMvHasse.le.MulPow2SumRothMvL1.of.RothMvIndex P (u s + v t) r hP


-- created on 2026-10-21
