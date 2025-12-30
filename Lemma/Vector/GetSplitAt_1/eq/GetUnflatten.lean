import sympy.vector.vector
import Lemma.Bool.HEq.of.All_Eq.Eq.Eq
import Lemma.List.Prod.eq.Foldr
import Lemma.Bool.HEq.of.All_HEq.Eq
import Lemma.Bool.EqImpS_Decidable.of.Eq
open List Bool


@[main, comm]
private lemma main
-- given
  (v : List.Vector α (n :: s).prod)
  (i : Fin n) :
-- imply
  (v.splitAt 1)[i] = v.unflatten[i] := by
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
  (v.splitAt 1).get ⟨i, by simp⟩ = v.unflatten.get i :=
-- proof
  main v i


-- created on 2025-07-16
