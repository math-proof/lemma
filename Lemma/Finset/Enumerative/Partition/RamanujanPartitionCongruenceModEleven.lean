import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven
open MetaMathlibExt


/--
[ramanujan_partition_congruence_mod_eleven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujan_partition_congruence_mod_eleven_eq
  {m : ℕ} :
-- imply
  Fintype.card (Nat.Partition (11 * m + 6)) ≡ 0 [MOD 11] := by
-- proof
  apply MetaMathlibExt.ramanujan_partition_congruence_mod_eleven m


-- created on 2026-10-20
