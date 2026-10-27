import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part10
open List
open MetaMathlibExt


namespace MetaMathlibExt

/--
[partitions_two_distant_eq_polarized](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean)
-/
@[path]
lemma partitions_two_distant_eq_polarized
  {n : ℕ} :
-- imply
  Fintype.card {p : Nat.Partition n //
    p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b} =
    Fintype.card {p : Nat.Partition n //
    p.parts.Nodup ∧ ∀ e ∈ p.parts, e % 2 = 0 →
    2 * (p.parts.filter (fun i => i % 2 = 1)).card < e} :=
-- proof
  Fintype.card_congr ((TwoDistantPolarized.e1 n).trans (TwoDistantPolarized.e2 n))

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
