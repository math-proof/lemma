module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.Combinatorics.Enumerative.NarayanaPolynomial

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[narayanaPolynomialCoeff_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/NarayanaPolynomial.lean)
-/
@[path]
public theorem narayanaPolynomialCoeff_succ_succ
  {n k : ℕ} :
-- imply
  narayanaPolynomialCoeff (n + 1) (k + 1) =
    narayana ⟨n + 1, Nat.succ_pos n⟩ ⟨k + 1, Nat.succ_pos k⟩ :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
