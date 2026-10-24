import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.Landau
open Nat
open Partition


namespace Nat.Partition

/--
[partsLCM_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
lemma partsLCM_zero
  {p : Partition 0} :
-- imply
  p.partsLCM = 1 := by
-- proof
  simp [partsLCM]

end Nat.Partition

namespace Nat.Partition

/--
[partsLCM_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
lemma partsLCM_one
  {p : Partition 1} :
-- imply
  p.partsLCM = 1 := by
-- proof
  simp [partsLCM]

end Nat.Partition

namespace Nat

/--
[Partition.partsLCM_le_landauFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
lemma Partition.partsLCM_le_landauFunction
  {n : ℕ}
  {p : n.Partition} :
-- imply
  p.partsLCM ≤ landauFunction n :=
-- proof
Finset.le_sup (Finset.mem_univ p)

end Nat

namespace Nat

/--
[exists_partition_partsLCM_eq_landauFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
lemma exists_partition_partsLCM_eq_landauFunction
  {n : ℕ} :
-- imply
  ∃ p : n.Partition, p.partsLCM = landauFunction n := by
-- proof
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset n.Partition)
    ⟨Partition.indiscrete n, Finset.mem_univ _⟩ Partition.partsLCM
  exact ⟨p, hp.symm⟩

end Nat

namespace Nat

/--
[landauFunction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
lemma landauFunction_zero
  :
-- imply
  landauFunction 0 = 1 := by
-- proof
  simp [landauFunction]

end Nat

namespace Nat

/--
[landauFunction_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean)
-/
@[path]
lemma landauFunction_one
  :
-- imply
  landauFunction 1 = 1 := by
-- proof
  simp [landauFunction]

end Nat


-- created on 2026-10-20
-- updated on 2026-10-23
