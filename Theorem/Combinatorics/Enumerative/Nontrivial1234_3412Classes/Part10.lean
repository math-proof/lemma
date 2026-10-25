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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part10


namespace MetaMathlibExt

lemma ntSemi_iff_breaks_empty {n : ℕ} (hn : 0 < n)
    (π : Equiv.Perm (Fin n)) : ntSemi π ↔ ntBreaks π = ∅ := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ntBeta_breaks_eq_empty hj
  · exact nt_exists_beta_of_breaks_empty hn

lemma ntBreaks_ins_eq_triple {m : ℕ} (hm : 0 < m)
    (p v : Fin (m + 1)) (ρ : Equiv.Perm (Fin m))
    (hρ : ntBreaks ρ = ∅) (hnot : ¬ntSemi (ntIns p v ρ)) :
    ntBreaks (ntIns p v ρ) =
      {(finRotate (m + 1)).symm p, p,
        (ntIns p v ρ).symm (finRotate (m + 1) v)} := by
  let α := ntIns p v ρ
  have hsub : ntBreaks α ⊆
      {(finRotate (m + 1)).symm p, p, α.symm (finRotate (m + 1) v)} :=
    ntBreaks_ins_subset hm p v ρ hρ
  have htriple :
      ({(finRotate (m + 1)).symm p, p,
        α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1))).card ≤ 3 := by
    have hA := Finset.card_insert_le ((finRotate (m + 1)).symm p)
      ({p, α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1)))
    have hB := Finset.card_insert_le p
      ({α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1)))
    have hC : ({α.symm (finRotate (m + 1) v)} : Finset (Fin (m + 1))).card = 1 := by
      simp
    omega
  have hle : (ntBreaks α).card ≤ 3 :=
    le_trans (Finset.card_le_card hsub) htriple
  have h0 : (ntBreaks α).card ≠ 0 := by
    intro h
    apply hnot
    rw [ntSemi_iff_breaks_empty (by omega)]
    exact Finset.card_eq_zero.mp h
  have h1 : (ntBreaks α).card ≠ 1 := nt_card_breaks_ne_one α
  have h2 : (ntBreaks α).card ≠ 2 := nt_card_breaks_ne_two α
  have hcard : (ntBreaks α).card = 3 := by omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcard]
  exact htriple

end MetaMathlibExt
