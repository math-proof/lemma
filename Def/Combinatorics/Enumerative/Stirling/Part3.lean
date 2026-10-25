/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Stirling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Theorem.Combinatorics.Enumerative.Stirling.Part2
/-!
# Permutations and unsigned Stirling numbers

This file identifies unsigned Stirling numbers of the first kind with permutations having a
prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

noncomputable def decomposeFinQuotientEquiv {n : ℕ} (q : Fin n)
    (e : Equiv.Perm (Fin n)) :
    Quotient (Equiv.Perm.SameCycle.setoid
      (Equiv.Perm.decomposeFin.symm (q.succ, e))) ≃
      Quotient (Equiv.Perm.SameCycle.setoid e) := by
  let mapCycle :
      Quotient (Equiv.Perm.SameCycle.setoid
        (Equiv.Perm.decomposeFin.symm (q.succ, e))) →
        Quotient (Equiv.Perm.SameCycle.setoid e) :=
    Quotient.map (dropFin q)
    (fun {a b} h => show e.SameCycle (dropFin q a) (dropFin q b) from
      (decomposeFin_sameCycle_iff q e a b).mp h)
  refine Equiv.ofBijective mapCycle ?_
  constructor
  · intro a b hab
    refine Quotient.inductionOn₂ a b ?_ hab
    intro x y hxy
    apply Quotient.sound
    apply (decomposeFin_sameCycle_iff q e x y).mpr
    change (Quotient.mk _ (dropFin q x) :
      Quotient (Equiv.Perm.SameCycle.setoid e)) = Quotient.mk _ (dropFin q y) at hxy
    exact Quotient.exact hxy
  · intro a
    refine Quotient.inductionOn a ?_
    intro x
    exact ⟨Quotient.mk _ x.succ, rfl⟩

end MetaMathlibExt
