import Initialize.Tactic.Attr.Basic


@[path, comm, mp, mpr]
private lemma main
  [AddMonoidWithOne R]
  [CharZero R]
  {a b : ℕ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Nat.cast_inj


-- created on 2025-04-11
-- updated on 2026-10-26
