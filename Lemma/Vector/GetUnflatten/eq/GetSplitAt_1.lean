import sympy.vector.vector
import Lemma.Logic.HEq.of.All_Eq.Eq.Eq
import Lemma.List.Prod.eq.Foldr
import Lemma.Logic.HEq.of.All_HEq.Eq
import Lemma.Logic.EqImpS_Decidable.of.Eq
open Logic List


@[main, comm]
private lemma main
-- given
  (v : List.Vector α (n :: s).prod)
  (i : Fin n) :
-- imply
  v.unflatten[i] = (v.splitAt 1)[i] := by
-- proof
  unfold List.Vector.splitAt
  simp
  congr
  ·
    simp
  ·
    apply HEq.of.All_Eq.Eq.Eq _ rfl
    ·
      simp_all
    ·
      simp [Prod.eq.Foldr]
  repeat simp


@[main, comm]
private lemma fin
-- given
  (v : List.Vector α (n :: s).prod)
  (i : Fin n) :
-- imply
  v.unflatten.get i = (v.splitAt 1).get ⟨i, by simp⟩ := by
-- proof
  apply main


-- created on 2025-07-16
