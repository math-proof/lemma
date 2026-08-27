import Lemma.Vector.ValGet.eq.ValArraySliceFlatten
import Lemma.Vector.ValArraySlice.eq.ArraySliceVal
open Vector


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  v[i].val = (v.toList.map List.Vector.toList).flatten.array_slice (i * n) n := by
-- proof
  rw [ValGet.eq.ValArraySliceFlatten v i]
  rw [ValArraySlice.eq.ArraySliceVal]
  rfl


-- created on 2025-05-27
-- updated on 2026-08-24
