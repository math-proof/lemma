import Lemma.Set.In_Iio.is.Lt
open Set


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (x a : α) :
-- imply
  x ∈ Iio a ↔ a > x := by
-- proof
  apply In_Iio.is.Lt


-- created on 2025-04-27
-- updated on 2025-08-02
