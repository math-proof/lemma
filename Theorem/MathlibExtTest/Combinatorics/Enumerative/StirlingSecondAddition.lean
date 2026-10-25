/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/StirlingSecondAddition.lean -/


import Lemma.Finset.Enumerative.StirlingSecondAddition


namespace MetaMathlibExt

example (u v : ℕ) (hu : 0 < u) : Nat.stirlingSecond (u + v) 0 = 0 := by
  simpa using stirlingSecond_addition u v 0 hu

example (u v k : ℕ) (hu : 0 < u) :
    Nat.stirlingSecond (u + v) k =
      ∑ n ∈ Finset.Icc 1 k, Nat.stirlingSecond u n *
        ∑ m ∈ Finset.Icc (k - n) v,
          Nat.choose v m * Nat.stirlingSecond m (k - n) * n ^ (v - m) :=
  stirlingSecond_addition u v k hu

#print axioms stirlingSecond_addition

end MetaMathlibExt
