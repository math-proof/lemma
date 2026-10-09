import Lemma.Vector.Head.eq.Get_0
open Vector


@[path, comm]
private lemma main
-- given
  (s : List.Vector α (.succ n)) :
-- imply
  s[0] ::ᵥ s.tail = s := by
-- proof
  let ⟨s, _⟩ := s
  match s with
  | [] =>
    contradiction
  | head :: tail =>
    constructor


@[path, comm]
private lemma head
-- given
  (s : List.Vector α (.succ n)) :
-- imply
  s.head ::ᵥ s.tail = s := by
-- proof
  rw [Vector.Head.eq.Get_0]
  apply main


-- created on 2025-05-08
-- updated on 2025-05-10
