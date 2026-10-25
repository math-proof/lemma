/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Theorem.Combinatorics.BellWeakExcedance.Part3


section

namespace MetaMathlibExt

def fiberEquiv {n : ℕ} {S B : Finset (Fin n)} (m0 : Fin n)
    (hmB : m0 ∈ B) (hBsub : B ⊆ S) :
    { P : Finpartition S // P.part m0 = B } ≃ Finpartition (S \ B) where
  toFun x :=
    removeBlock x.1
      (by
        have hmem : x.1.part m0 ∈ x.1.parts :=
          x.1.part_mem.mpr (hBsub hmB)
        rw [x.2] at hmem
        exact hmem)
  invFun Q :=
    ⟨addBlock hBsub ⟨m0, hmB⟩ Q,
      addBlock_part hBsub ⟨m0, hmB⟩ Q m0 hmB⟩
  left_inv x := by
    obtain ⟨P, hP⟩ := x
    have hBmem : B ∈ P.parts := by
      have hmem : P.part m0 ∈ P.parts := P.part_mem.mpr (hBsub hmB)
      rw [hP] at hmem
      exact hmem
    have hEq : addBlock hBsub ⟨m0, hmB⟩ (removeBlock P hBmem) = P :=
      add_remove_cancel P hBmem hBsub ⟨m0, hmB⟩
    exact Subtype.ext hEq
  right_inv Q := remove_add_cancel hBsub ⟨m0, hmB⟩ Q m0 hmB

/-! ## Part B: Valid perms biject with Finpartitions -/

noncomputable def toPart (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Finpartition (Finset.univ : Finset (Fin n)) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker (root n σ))

end MetaMathlibExt
end
