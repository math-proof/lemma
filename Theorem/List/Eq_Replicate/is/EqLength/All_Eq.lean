module

public import Initialize.Tactic.Attr.Basic

public section


@[mp, mpr]
public theorem List.Eq_Replicate.is.EqLength.All_Eq
-- given
  (l : List α)
  (n : ℕ)
  (a : α) :
-- imply
  l = List.replicate n a ↔ l.length = n ∧ ∀ b ∈ l, b = a :=
-- proof
  List.eq_replicate_iff


-- created on 2025-08-02
