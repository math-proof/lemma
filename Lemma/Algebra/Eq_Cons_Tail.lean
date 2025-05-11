import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
-- given
  (v : List.Vector α (Nat.succ n)) :
-- imply
  v = v[0] ::ᵥ v.tail := by
-- proof
  let ⟨v, _⟩ := v
  match v with
  | [] =>
    contradiction
  | v₀ :: tail =>
    constructor


-- created on 2025-05-08
-- updated on 2025-05-10
