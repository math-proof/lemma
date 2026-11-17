module

public import Mathlib
public import Def.Combinatorics.FineNumber

public section

open MetaMathlibExt


namespace MetaMathlibExt

/--
[fineNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FineNumber.lean)
-/
public theorem fineNumber_eq_sum
  {n : Nat} :
-- imply
  fineNumber n = (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ) :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
