import sympy.core.numbers
import Lemma.Algebra.Eq_Ceil.of.Gt_Arg
import Lemma.Complex.GtAddArgS.of.EqCeilSubDivS
open Algebra Complex


@[main]
private lemma main
  {A B : ℂ} :
-- imply
  arg A + arg B > π ↔ ⌈(arg A + arg B) / (2 * π) - 1 / 2⌉ = 1 :=
-- proof
  ⟨Eq_Ceil.of.Gt_Arg, GtAddArgS.of.EqCeilSubDivS⟩


-- created on 2018-10-31
-- updated on 2026-08-20
