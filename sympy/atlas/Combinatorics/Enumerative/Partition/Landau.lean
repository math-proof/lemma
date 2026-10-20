/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/Landau.lean -/

import Mathlib.Algebra.GCDMonoid.Multiset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The Landau function

The Landau function is the maximum least common multiple of the parts of an
integer partition of `n`.

## References

- [E. Rowland, M. Stipulanti, R. Yassawi, *An elementary proof of Bridy's
  theorem*](https://arxiv.org/abs/2308.10977)
-/

namespace Nat

namespace Partition

/-- The least common multiple of the parts of an integer partition. -/
def partsLCM {n : ℕ} (p : n.Partition) : ℕ :=
  p.parts.lcm

@[simp]
theorem partsLCM_zero (p : Partition 0) : p.partsLCM = 1 := by
  simp [partsLCM]

@[simp]
theorem partsLCM_one (p : Partition 1) : p.partsLCM = 1 := by
  simp [partsLCM]

end Partition

/-- The maximum least common multiple of the parts of a partition of `n`. -/
def landauFunction (n : ℕ) : ℕ :=
  Finset.univ.sup (fun p : n.Partition => p.partsLCM)

/-- The LCM of the parts of any partition is bounded by the Landau function. -/
theorem Partition.partsLCM_le_landauFunction {n : ℕ} (p : n.Partition) :
    p.partsLCM ≤ landauFunction n := by
  exact Finset.le_sup (Finset.mem_univ p)

/-- Some partition attains the value of the Landau function. -/
theorem exists_partition_partsLCM_eq_landauFunction (n : ℕ) :
    ∃ p : n.Partition, p.partsLCM = landauFunction n := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset n.Partition)
    ⟨Partition.indiscrete n, Finset.mem_univ _⟩ Partition.partsLCM
  exact ⟨p, hp.symm⟩

@[simp]
theorem landauFunction_zero : landauFunction 0 = 1 := by
  simp [landauFunction]

@[simp]
theorem landauFunction_one : landauFunction 1 = 1 := by
  simp [landauFunction]

end Nat
