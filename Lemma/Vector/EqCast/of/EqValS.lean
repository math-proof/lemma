import Lemma.Bool.EqUFnS.of.Eq
import Lemma.Vector.Eq.of.EqValS
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector Bool


@[main, comm 1]
private lemma main
  {a : List.Vector α n}
  {b : List.Vector α m}
-- given
  (h_eq : a.val = b.val) :
-- imply
  cast (congrArg (List.Vector α ) (Eq.of.EqValS.nat h_eq)) a = b := by
-- proof
  let ⟨a, ha⟩ := a
  let ⟨b, hb⟩ := b
  simp at h_eq
  subst h_eq
  have h_mn := ha.symm.trans hb
  ext i
  rw [GetCast.eq.Get.of.Eq.fin h_mn]
  aesop


-- created on 2025-05-23
