import Lemma.Trigonometry.Arg.eq.Ite__Ite_Arcsin
import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.BFn_Ite.is.Imp.Imp
import Lemma.Logic.ImpEq.is.ImpEq
import Lemma.Logic.Ne.is.NotEq
import Lemma.Trigonometry.Arg.eq.Ite__Ite_Arccos.of.Ne_0
open Logic Trigonometry


@[main]
private lemma main
  {z : ℂ} :
-- imply
  arg z =
    if z = 0 then
      0
    else if im z ≥ 0 then
      arccos (re z / ‖z‖)
    else
      -arccos (re z / ‖z‖) := by
-- proof
  rw [BFn_Ite.is.Imp.Imp (R := Eq)]
  constructor
  rw [ImpEq.is.ImpEq.subst (p := fun z => arg z = 0)]
  simp
  rw [NotEq.is.Ne]
  intro h_ne
  apply Arg.eq.Ite__Ite_Arccos.of.Ne_0 h_ne


-- created on 2025-01-05
