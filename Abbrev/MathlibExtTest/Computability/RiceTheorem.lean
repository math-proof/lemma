/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean -/


module

public import Mathlib.Computability.PartrecCode
public import Theorem.Nat.RiceTheorem
@[expose] public section


abbrev riceTheoremTest_standardNumbering (e : ℕ) : ℕ →. ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e)

