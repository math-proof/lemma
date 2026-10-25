/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part12


namespace MetaMathlibExt

lemma nt_mem_breaks_beta_doubleSwap_iff {n j : ℕ} (hj : j + 1 ≤ n)
    {a b c d i : Fin n} :
    i ∈ ntBreaks (ntBeta n j hj * (Equiv.swap a c * Equiv.swap b d)) ↔
      (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n)) (finRotate n i) ≠
        finRotate n ((Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n)) i) := by
  let _ : NeZero n := ⟨by omega⟩
  let δ := (Equiv.swap a c * Equiv.swap b d : Equiv.Perm (Fin n))
  have hgood (x : Fin n) :
      ntBeta n j hj (finRotate n x) = (finRotate n).symm (ntBeta n j hj x) := by
    by_contra h
    have hx := (nt_mem_breaks_iff (ntBeta n j hj) x).2 h
    rw [ntBeta_breaks_eq_empty hj] at hx
    simp at hx
  rw [nt_mem_breaks_iff]
  change ntBeta n j hj (δ (finRotate n i)) ≠
    (finRotate n).symm (ntBeta n j hj (δ i)) ↔ _
  rw [← hgood (δ i)]
  exact (ntBeta n j hj).injective.ne_iff

end MetaMathlibExt
