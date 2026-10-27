import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLocalMarkedDisagreementSwitch
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[sixVertexLocalMarkedPatternWeight_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalMarkedDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalMarkedPatternWeight_eq_pow_eq
  {p : SixVertexLocalIncomingPattern}
-- given
  (hp : p.Ice) :
-- imply
  sixVertexLocalMarkedPatternWeight p = (C 2 + X) ^ (if p.IsCType then 1 else 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalMarkedPatternWeight_eq_pow p hp

/--
[sixVertexLocalMarkedPatternWeight_mul_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalMarkedDisagreementSwitch.lean)
-/
@[path]
private lemma sixVertexLocalMarkedPatternWeight_mul_eq_pow_eq
  {p q : SixVertexLocalIncomingPattern}
-- given
  (hp : p.Ice)
  (hq : q.Ice) :
-- imply
  sixVertexLocalMarkedPatternWeight p * sixVertexLocalMarkedPatternWeight q = (C 2 + X) ^ sixVertexLocalCTypeCount p q := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalMarkedPatternWeight_mul_eq_pow p q hp hq

/--
[coeff_two_add_X_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalMarkedDisagreementSwitch.lean)
-/
@[path]
private lemma coeff_two_add_X_pow_eq
  {m k : Nat} :
-- imply
  ((C 2 + X : Real[X]) ^ m).coeff k = (2 : Real) ^ (m - k) * m.choose k := by
-- proof
  apply StatMech.FrontierD.coeff_two_add_X_pow m k

/--
[coeff_two_add_X_pow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalMarkedDisagreementSwitch.lean)
-/
@[path]
private lemma coeff_two_add_X_pow_mono_eq
  {a b : Nat}
  {k : Nat}
-- given
  (hab : a <= b) :
-- imply
  ((C 2 + X : Real[X]) ^ a).coeff k <= ((C 2 + X : Real[X]) ^ b).coeff k := by
-- proof
  apply StatMech.FrontierD.coeff_two_add_X_pow_mono hab k

/--
[exists_sixVertexLocalSwapTwo_markedCoefficient_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLocalMarkedDisagreementSwitch.lean)
-/
@[path]
private lemma exists_sixVertexLocalSwapTwo_markedCoefficient_le_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hd : p d ≠ q d)
  (hnotCC : Not (p.IsCType /\ q.IsCType)) :
-- imply
  exists e : Fin 4, e ≠ d /\ p e ≠ q e /\ (sixVertexLocalSwapTwo p q d e).1.Ice /\ (sixVertexLocalSwapTwo p q d e).2.Ice /\ forall k, (sixVertexLocalMarkedPatternWeight p * sixVertexLocalMarkedPatternWeight q).coeff k <= (sixVertexLocalMarkedPatternWeight (sixVertexLocalSwapTwo p q d e).1 * sixVertexLocalMarkedPatternWeight (sixVertexLocalSwapTwo p q d e).2).coeff k := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexLocalSwapTwo_markedCoefficient_le p q d hp hq hd hnotCC


-- created on 2026-10-23
