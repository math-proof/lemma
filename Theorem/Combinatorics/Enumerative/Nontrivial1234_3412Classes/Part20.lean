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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part20


namespace MetaMathlibExt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in

lemma ntG7_of_eqvGen {σ τ : Equiv.Perm (Fin 7)}
    (hτ : τ ∈ ntG 6) (hστ : Relation.EqvGen (ntMove 7) σ τ) : σ ∈ ntG 6 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (ntClosed_mem (ntE_closed (m := 5)) hστ).2 hτ.1
  · let P : Set (Equiv.Perm (Fin 7)) := {π | ntPat 7 π}
    have hP : ∀ x ∈ P, ∀ y, (ntMove 7 x y ∨ ntMove 7 y x) → y ∈ P := by
      intro x _ y hxy
      exact ntMove_pat (Or.symm hxy)
    exact (ntClosed_mem hP hστ).2 hτ.2.1
  · intro j hj hσK
    by_cases hj0 : j = 0
    · subst j
      rw [ntK_zero_empty hj] at hσK
      exact hσK
    · have hj1 : 1 ≤ j := by omega
      have hK : ∀ x ∈ ntK 7 j hj, ∀ y,
          (ntMove 7 x y ∨ ntMove 7 y x) → y ∈ ntK 7 j hj := by
        intro x hx y hxy
        exact ntK_closed (by omega) hj1 hj hx hxy
      have hτK : τ ∈ ntK 7 j hj :=
        (ntClosed_mem hK hστ).1 hσK
      exact hτ.2.2 j hj hτK

lemma ntDist7_lt_memG (σ : Equiv.Perm (Fin 7))
    (hσ : ntDist7 (ntCode σ) < 15) : σ ∈ ntG 6 := by
  rcases ntDist7_reaches σ hσ with heven | hodd
  · exact ntG7_of_eqvGen (ntEven_memG (m := 5) (by omega)) heven
  · exact ntG7_of_eqvGen (ntOdd_memG (m := 5) (by omega)) hodd

/-- The `S_5` count. -/
lemma ntSmall5 : ntncl (ntMove 5) Set.univ = 9 := by
  apply ntNcl_eq_of_reps (x := ntRep5)
  · intro k
    simp
  · intro k
    exact (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).2
      (ntPat_move (ntRep5_pat k))
  · intro k l hkl hrel
    have hlabel := ntEqvGen_label_eq ntCertificate5 hrel
    rw [ntLabel_rep5, ntLabel_rep5] at hlabel
    exact hkl (Fin.ext hlabel)
  · intro z _ hnontrivial
    obtain ⟨w, hstep⟩ :=
      (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).1 hnontrivial
    have hpat : ntPat 5 z := ntMove_pat hstep
    have hlt : ntLabel5 (ntCode z) < 9 := ntPat_label_lt ntCertificate5 hpat
    let k : Fin 9 := ⟨ntLabel5 (ntCode z), hlt⟩
    refine ⟨k, ntDistance_reaches ntRep5 ntCode_rep5 ntCertificate5 z k ?_⟩
    rfl

/-- The `S_6` count. -/
lemma ntSmall6 : ntncl (ntMove 6) Set.univ = 26 := by
  apply ntNcl_eq_of_reps (x := ntRep6)
  · intro k
    simp
  · intro k
    exact (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).2
      (ntPat_move (ntRep6_pat k))
  · intro k l hkl hrel
    have hlabel := ntEqvGen_label_eq ntCertificate6 hrel
    rw [ntLabel_rep6, ntLabel_rep6] at hlabel
    exact hkl (Fin.ext hlabel)
  · intro z _ hnontrivial
    obtain ⟨w, hstep⟩ :=
      (ntNcl_nontrivial_iff (fun _ _ h => ntMove_ne h)).1 hnontrivial
    have hpat : ntPat 6 z := ntMove_pat hstep
    have hlt : ntLabel6 (ntCode z) < 26 := ntPat_label_lt ntCertificate6 hpat
    let k : Fin 26 := ⟨ntLabel6 (ntCode z), hlt⟩
    refine ⟨k, ntDistance_reaches ntRep6 ntCode_rep6 ntCertificate6 z k ?_⟩
    rfl

/-- Every generic element of `S_7` reaches a reference permutation. -/
lemma ntSmall7 {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ ntG 6) :
    Relation.EqvGen (ntMove 7) σ (ntEven 7) ∨
      Relation.EqvGen (ntMove 7) σ (ntOdd 5) := by
  have hok := (List.all_eq_true.mp ntCertificate7) (ntCode σ)
    (ntCode_mem_permutations' σ)
  have hG := ntIsGB_of_memG7 hσ
  dsimp only [ntOk7] at hok
  rw [Bool.and_eq_true] at hok
  have hlt : ntDist7 (ntCode σ) < 15 := by
    have hfirst := hok.1
    change (ntDist7 (ntCode σ) < 15 || !ntIsGB 7 (ntQuads 7) (ntCode σ)) =
      true at hfirst
    rw [hG] at hfirst
    simpa only [Bool.not_true, Bool.or_false, decide_eq_true_eq] using hfirst
  exact ntDist7_reaches σ hlt

end MetaMathlibExt
