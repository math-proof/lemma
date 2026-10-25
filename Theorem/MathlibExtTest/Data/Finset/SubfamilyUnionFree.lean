/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Data/Finset/SubfamilyUnionFree.lean -/


import Def.Data.Finset.SubfamilyUnionFree


-- The empty family is vacuously union-free.
example {α : Type*} [DecidableEq α] :
    (∅ : Finset (Finset α)).SubfamilyUnionFree :=
  fun A h _ _ => (Finset.notMem_empty A h).elim

-- A singleton family over a nonempty set is union-free: every proper
-- subfamily is empty, whose union is `∅ ≠ A`.
example {α : Type*} [DecidableEq α] (A : Finset α) (hA : A.Nonempty) :
    ({A} : Finset (Finset α)).SubfamilyUnionFree := by
  intro B hB T hT _
  obtain rfl : B = A := Finset.mem_singleton.mp hB
  have hTe : T = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have hx2 := hT hx
    rw [Finset.mem_erase, Finset.mem_singleton] at hx2
    exact hx2.1 hx2.2
  have hsup : (∅ : Finset (Finset α)).sup id = ∅ := by simp
  rw [hTe, hsup]
  exact fun h => Finset.nonempty_iff_ne_empty.mp hA h.symm

