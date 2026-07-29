import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Div.of.Eq
import Lemma.Rat.EqMul_Div.of.Ne_0
open Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.EqMul.is.Eq_Div.of.Ne_0 |
| comm | Rat.Eq_Div.is.EqMul.of.Ne_0 |
| mp   | Rat.Eq_Div.of.EqMul.Ne_0 |
| mpr  | Rat.EqMul.of.Eq_Div.Ne_0 |
| mp.comm | Rat.EqDiv.of.Eq_Mul.Ne_0 |
| mpr.comm | Rat.Eq_Mul.of.EqDiv.Ne_0 |
| comm.is | Rat.Eq_Mul.is.EqDiv.of.Ne_0 |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [GroupWithZero α]
  {b : α}
-- given
  (h₀ : b ≠ 0)
  (a c : α) :
-- imply
  a * b = c ↔ a = c / b := by
-- proof
  constructor <;>
    intro h
  ·
    exact EqDivMul.of.Ne_0 h₀ a ▸ Div.of.Eq h b
  ·
    subst h
    simp_all


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma left
  [CommGroupWithZero α]
  {a : α}
-- given
  (h₀ : a ≠ 0)
  (c b : α):
-- imply
  a * b = c ↔ b = c / a := by
-- proof
  constructor <;>
    intro h
  ·
    exact EqDivMul.of.Ne_0.left h₀ b ▸ Div.of.Eq h a
  ·
    subst h
    apply EqMul_Div.of.Ne_0 h₀


-- created on 2024-07-01
-- updated on 2025-12-10
