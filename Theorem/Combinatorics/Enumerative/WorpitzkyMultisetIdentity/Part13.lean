/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Fintype.Fin
import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part13


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
