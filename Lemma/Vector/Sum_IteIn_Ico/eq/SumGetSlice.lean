import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import Lemma.Vector.Sum.eq.Sum_Get
import sympy.vector.vector
open Vector
set_option maxHeartbeats 1000000


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (v : List.Vector α n)
  (a b : ℕ) :
-- imply
  ∑ k : Fin n, (if ↑k ∈ Ico a b then
    v[k]
  else
    0) = v[a:b].sum := by
-- proof
  rw [Sum.eq.Sum_Get.fin]
  have h_get_slice (i : ℕ) (h_i : i < b):= GetGetSlice.eq.Get.of.Lt.Lt.Dvd (by grind) (by grind) (by grind) v (j := a) (n := b) (d := 1) (i := i)
  conv_rhs =>
    arg 2
    ext i
    -- erw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd (by grind) (by grind) (by grind)]
  grind


-- created on 2026-08-08
