import Lemma.Vector.GetAdd.eq.AddGetS
open Vector


@[main]
private lemma main
  [Add α]
  [Add β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a + b) = f a + f b)
  (a b : List.Vector α n) :
-- imply
  (a + b).map f = a.map f + b.map f := by
-- proof
  ext i
  simp [GetAdd.eq.AddGetS.fin]
  rw [hf]


-- created on 2026-08-08
