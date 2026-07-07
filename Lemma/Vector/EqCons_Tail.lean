import sympy.vector.vector
import sympy.Basic


@[main, comm]
private lemma main
-- given
  (s : List.Vector α (.succ n)) :
-- imply
  s.head ::ᵥ s.tail = s := by
-- proof
  let ⟨v, _⟩ := s
  match v with
  | [] =>
    contradiction
  | h :: t =>
    constructor


-- created on 2026-07-06
