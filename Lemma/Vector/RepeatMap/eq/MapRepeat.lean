import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Vector.GetRepeat.eq.Get_Mod.of.Lt_Mul
open Vector


@[main, comm]
private lemma main
  {β : Type*}
-- given
  (v : List.Vector α n)
  (f : α → β)
  (d : ℕ) :
-- imply
  (v.map f).repeat d = (v.repeat d).map f := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  erw [GetMap.eq.UFnGet (i := i)]
  erw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
  erw [GetRepeat.eq.Get_Mod.of.Lt_Mul.fin]
  erw [GetMap.eq.UFnGet]


-- created on 2026-08-12
