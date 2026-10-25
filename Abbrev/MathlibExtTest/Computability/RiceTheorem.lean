/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Computability/RiceTheorem.lean -/


import Mathlib.Computability.PartrecCode
import Lemma.Nat.RiceTheorem


abbrev riceTheoremTest_standardNumbering (e : ℕ) : ℕ →. ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e)

