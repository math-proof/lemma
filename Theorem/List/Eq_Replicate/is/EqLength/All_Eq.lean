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



public theorem List.Eq_Replicate.of.EqLength.All_Eq
  {l : List α}
  {n : ℕ}
  {a : α}
  (h_len : l.length = n)
  (h_all : ∀ b ∈ l, b = a) :
  l = List.replicate n a :=
  (List.Eq_Replicate.is.EqLength.All_Eq l n a).mpr ⟨h_len, h_all⟩

-- created on 2025-08-02
