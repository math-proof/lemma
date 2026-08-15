import sympy.vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.MapGetSlice.eq.GetSliceMap |
| comm | Vector.GetSliceMap.eq.MapGetSlice |
-/
@[main, comm]
private lemma main
  {β : Type*}
-- given
  (v : List.Vector α n)
  (f : α → β)
  (s : Slice) :
-- imply
  (v.getSlice s).map f = (v.map f).getSlice s := by
-- proof
  ext t
  unfold List.Vector.getSlice
  simp [GetElem.getElem, List.Vector.length, List.Vector.get_map]


-- created on 2026-08-15
