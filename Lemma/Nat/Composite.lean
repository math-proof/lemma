import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Composite
open Nat


namespace Nat

/--
[IsComposite.one_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Composite.lean)
-/
@[path]
lemma IsComposite.one_lt
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
@[path]
lemma IsComposite.not_prime
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
