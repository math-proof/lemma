import sympy.sets.sets
import Lemma.Set.In_Ico.is.Le.Lt
import Lemma.Set.Lt.of.In_Ioc
import Lemma.Set.Le.of.In_Ioc
import Lemma.Int.GeCeil
import Lemma.Rat.LeFloor
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Nat.Lt_Add_1.of.Le
open Set Rat Int Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b x : α}
-- given
  (h : x ∈ Ioc a b) :
-- imply
  ⌈x⌉ ∈ Ico (⌊a⌋ + 1) (⌈b⌉ + 1) := by
-- proof
  apply In_Ico.of.Le.Lt
  ·
    have h_lt : (⌊a⌋ : α) < (⌈x⌉ : α) :=
      lt_of_lt_of_le (lt_of_le_of_lt (LeFloor a) (Lt.of.In_Ioc h)) (Le_Ceil (x := x))
    exact Int.add_one_le_iff.mpr (Lt.of.LtCoeS (R := α) h_lt)
  ·
    exact Lt_Add_1.of.Le (Int.ceil_mono (Le.of.In_Ioc h))


-- created on 2018-10-24
-- updated on 2026-08-22
