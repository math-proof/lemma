module
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.List.Indexes
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/
namespace MetaMathlibExt.TwoDistantPolarized

open List

noncomputable def oddm {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (fun x => x % 2 = 1)

noncomputable def evenm {n : ℕ} (p : Nat.Partition n) : Multiset ℕ :=
  p.parts.filter (fun x => x % 2 = 0)

noncomputable def Pl {n : ℕ} (p : Nat.Partition n) : List ℕ := (oddm p).sort (· ≤ ·)

noncomputable def Ql {n : ℕ} (p : Nat.Partition n) : List ℕ := (evenm p).sort (· ≤ ·)

end MetaMathlibExt.TwoDistantPolarized
