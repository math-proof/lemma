import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.TwoDistantPolarized
open List
open MetaMathlibExt


/--
[partitions_two_distant_eq_polarized](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean)
-/
@[path]
private lemma partitions_two_distant_eq_polarized_eq
  {n : ℕ} :
-- imply
  Fintype.card {p : Nat.Partition n //
    p.parts.Nodup ∧ ∀ a ∈ p.parts, ∀ b ∈ p.parts, a < b → a + 2 ≤ b} =
    Fintype.card {p : Nat.Partition n //
    p.parts.Nodup ∧ ∀ e ∈ p.parts, e % 2 = 0 →
    2 * (p.parts.filter (fun i => i % 2 = 1)).card < e} := by
-- proof
  apply MetaMathlibExt.partitions_two_distant_eq_polarized n


-- created on 2026-10-20
