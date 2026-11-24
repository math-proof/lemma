module
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Fintype.Fin
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

theorem wmiDesClass_le_max {m K : ℕ} (w : Fin K → Fin m) :
    wmiDesClass w ≤ max 1 K :=
  wmi_descent_succ_le_max w

theorem wmi_regroup (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    (∑ w : wmiWords m k,
      Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i)) =
      ∑ p ∈ Finset.Icc 1 (max 1 (∑ i, k i)),
        Nat.choose (x + (∑ i, k i) - p) (∑ i, k i) *
          Fintype.card { w : wmiWords m k // wmiDesClass w.1 = p } := by
  classical
  have hmap : ∀ w ∈ (Finset.univ : Finset (wmiWords m k)),
      wmiDesClass w.1 ∈ Finset.Icc 1 (max 1 (∑ i, k i)) := by
    intro w _
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by
      unfold wmiDesClass
      omega), wmiDesClass_le_max w.1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun w => Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.card_subtype]
  calc
    (∑ w ∈ (Finset.univ.filter (fun w : wmiWords m k => wmiDesClass w.1 = p)),
        Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i)) =
        ∑ _w ∈ (Finset.univ.filter
          (fun w : wmiWords m k => wmiDesClass w.1 = p)),
          Nat.choose (x + (∑ i, k i) - p) (∑ i, k i) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [(Finset.mem_filter.mp hw).2]
    _ = _ := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]

end MetaMathlibExt
end
