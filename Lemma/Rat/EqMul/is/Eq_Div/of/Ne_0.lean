import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Rat.EqMul_Div.of.Ne_0
open Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.EqMul.is.Eq\_Div.of.Ne\_0 |
| comm | Rat.Eq\_Div.is.EqMul.of.Ne\_0 |
| mp   | Rat.Eq\_Div.of.EqMul.Ne\_0 |
| mpr  | Rat.EqMul.of.Eq\_Div.Ne\_0 |
| mp.comm | Rat.EqDiv.of.Eq\_Mul.Ne\_0 |
| mpr.comm | Rat.Eq\_Mul.of.EqDiv.Ne\_0 |
| comm.is | Rat.Eq\_Mul.is.EqDiv.of.Ne\_0 |
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
    exact EqDivMul.of.Ne_0 h₀ a ▸ EqDivS.of.Eq h b
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
    exact EqDivMul.of.Ne_0.left h₀ b ▸ EqDivS.of.Eq h a
  ·
    subst h
    apply EqMul_Div.of.Ne_0 h₀


-- created on 2024-07-01
-- updated on 2025-12-10
