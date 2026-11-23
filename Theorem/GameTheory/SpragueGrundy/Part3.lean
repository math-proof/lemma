/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.WellFounded
public import Mathlib.Order.Lattice.Nat
public import Def.GameTheory.SpragueGrundy.Part2

public section

namespace MetaMathlibExt.SpragueGrundy

theorem mex_not_mem (s : Finset ℕ) : mex s ∉ s :=
  Nat.find_spec (exists_not_mem s)

theorem mex_le_of_not_mem (s : Finset ℕ) {m : ℕ} (h : m ∉ s) : mex s ≤ m :=
  Nat.find_min' (exists_not_mem s) h

theorem mem_of_lt_mex (s : Finset ℕ) {m : ℕ} (h : m < mex s) : m ∈ s := by
  by_contra hc
  exact absurd (mex_le_of_not_mem s hc) (not_le_of_gt h)

theorem mex_empty : mex ∅ = 0 :=
  Nat.le_zero.mp (mex_le_of_not_mem _ (Finset.notMem_empty 0))

theorem mex_range (n : ℕ) : mex (Finset.range n) = n := by
  apply Nat.le_antisymm
  · apply mex_le_of_not_mem
    rw [Finset.mem_range]
    exact Nat.lt_irrefl n
  · by_contra hle
    have hlt : mex (Finset.range n) < n := Nat.lt_of_not_ge hle
    have hmem : mex (Finset.range n) ∈ Finset.range n :=
      Finset.mem_range.mpr hlt
    exact mex_not_mem _ hmem

end MetaMathlibExt.SpragueGrundy
