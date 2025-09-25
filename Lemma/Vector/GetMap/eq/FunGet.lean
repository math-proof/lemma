import Lemma.Basic


@[main]
private lemma main
  {β : Type*}
-- given
  (v : List.Vector α n)
  (f : α → β)
  (i : Fin n) :
-- imply
  (v.map f).get i = f (v.get i) := by
-- proof
  simp [List.Vector.get_map]


-- created on 2024-07-01
