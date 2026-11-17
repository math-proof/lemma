module

public import Mathlib
public import Def.NumberTheory.Composite

public section

open Nat


namespace Nat

/--
[IsComposite.one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Composite.lean)
-/
public theorem IsComposite.one_lt
  {n : ℕ}
-- given
  (h : n.IsComposite) :
-- imply
  1 < n :=
-- proof
  h.1

end Nat

namespace Nat

/--
[IsComposite.not_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Composite.lean)
-/
public theorem IsComposite.not_prime
  {n : ℕ}
-- given
  (h : n.IsComposite) :
-- imply
  ¬ n.Prime :=
-- proof
  h.2

end Nat


-- created on 2026-10-20
-- updated on 2026-10-26
