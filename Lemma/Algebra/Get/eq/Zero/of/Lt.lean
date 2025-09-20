import Lemma.Algebra.Get.eq.Zero.of.Eq_0.Lt
open Algebra


@[main]
private lemma main
  [Zero α]
-- given
  (h_i : i < n) :
-- imply
  (0 : List.Vector α n)[i] = 0 := by
-- proof
  apply Get.eq.Zero.of.Eq_0.Lt
  rfl


-- created on 2025-09-04
