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
import Def.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part21


namespace MetaMathlibExt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in

/-- Deletion: every generic element is an insertion of a smaller generic one. -/
lemma ntDeletion {k : ℕ} (hk : 6 ≤ k) {σ : Equiv.Perm (Fin (k + 2))}
    (hσ : σ ∈ ntG (k + 1)) :
    ∃ y : Fin (k + 2), ∃ ρ ∈ ntG k, σ = ntIns y (σ y) ρ := by
  by_cases h : k = 6
  · subst k
    have hvne : (σ 0).val ≠ 7 := by
      intro hv
      apply hσ.1.1
      apply Fin.ext
      simpa using hv
    have hvlt : (σ 0).val < 7 := by
      have := (σ 0).is_lt
      omega
    let v : Fin 7 := ⟨(σ 0).val, hvlt⟩
    obtain ⟨ρ, hσρ⟩ := ntIns_exists 0 (σ 0) σ rfl
    have hok := (List.all_eq_true.mp (ntDeletionCertificate v)) (ntCode ρ)
      (ntCode_mem_permutations' ρ)
    dsimp only [ntDeletionSliceOk] at hok
    have hfull : ntInsertCodeZero v.val (ntCode ρ) = ntCode σ := by
      rw [hσρ, ntCode_ins_zero]
    rw [hfull] at hok
    generalize hyval : ntDeletionChoice (ntCode σ) = y at hok
    by_cases hy : y < 8
    · rw [ite_eq_left hy] at hok
      have hdist : ntDist7 (ntDeleteCode (ntCode σ) y) < 15 := by
        simpa only [decide_eq_true_eq] using hok
      let Y : Fin 8 := ⟨y, hy⟩
      obtain ⟨τ, hστ⟩ := ntIns_exists Y (σ Y) σ rfl
      have hdelete : ntDeleteCode (ntCode σ) y = ntCode τ := by
        rw [hστ]
        exact ntDeleteCode_ins Y (σ Y) τ
      have hτdist : ntDist7 (ntCode τ) < 15 := by
        rwa [hdelete] at hdist
      exact ⟨Y, τ, ntDist7_lt_memG τ hτdist, hστ⟩
    · rw [ite_eq_right hy, ntIsGB_of_memG8 hσ] at hok
      simp at hok
  · exact ntDeletion_large (by omega) hσ

/-- Every generic element reaches a reference permutation. -/
lemma ntG_two (m : ℕ) {σ : Equiv.Perm (Fin (m + 7))}
    (hσ : σ ∈ ntG (m + 6)) :
    Relation.EqvGen (ntMove (m + 7)) σ (ntEven (m + 7)) ∨
      Relation.EqvGen (ntMove (m + 7)) σ (ntOdd (m + 5)) := by
  induction m with
  | zero => exact ntSmall7 hσ
  | succ m IH =>
    have hE := hσ.1
    obtain ⟨y, ρ, hρ, heq⟩ := ntDeletion (k := m + 6) (by omega) hσ
    have hyv : (y ≠ 0 ∨ σ y ≠ Fin.last (m + 5 + 2)) ∧
        (y ≠ Fin.last (m + 5 + 2) ∨ σ y ≠ 0) := by
      constructor
      · by_cases hy : y = 0
        · refine Or.inr ?_
          intro hcon
          rw [hy] at hcon
          exact hE.1 hcon
        · exact Or.inl hy
      · by_cases hy : y = Fin.last (m + 5 + 2)
        · refine Or.inr ?_
          intro hcon
          rw [hy] at hcon
          exact hE.2 hcon
        · exact Or.inl hy
    have hIH : ∀ ρ ∈ ntG (m + 5 + 1),
        Relation.EqvGen (ntMove (m + 5 + 2)) ρ (ntEven (m + 5 + 2)) ∨
          Relation.EqvGen (ntMove (m + 5 + 2)) ρ (ntOdd (m + 5)) :=
      fun ρ hρ => IH hρ
    have hm55 : 5 ≤ m + 5 := by omega
    rw [heq]
    exact ntInsertion (m := m + 5) hm55 hIH hρ hyv

/-- The extreme-avoiding count is `n + 1`. -/
lemma ntE_formula (m : ℕ) :
    ntncl (ntMove (m + 7)) (ntE (m + 6)) = m + 8 := by
  have hjpf : ∀ t : Fin (m + 6), t.val + 1 + 1 ≤ m + 7 := by
    intro t
    have ht := t.is_lt
    omega
  have hex : ∀ t : Fin (m + 6), ∃ hub ∈ ntK (m + 7) (t.val + 1) (hjpf t),
      ∀ κ ∈ ntK (m + 7) (t.val + 1) (hjpf t),
        Relation.EqvGen (ntMove (m + 7)) κ hub := by
    intro t
    have ht := t.is_lt
    exact ntK_hub (by omega) (by omega) (hjpf t)
  choose hub hhubmem hhubreach using hex
  have hsub : ∀ t : Fin (m + 6),
      ntK (m + 7) (t.val + 1) (hjpf t) ⊆ ntE (m + 6) := by
    intro t
    have ht := t.is_lt
    exact ntK_sub_E (by omega) (hjpf t)
  have hirr : ∀ a b : Equiv.Perm (Fin (m + 7)),
      ntMove (m + 7) a b → a ≠ b :=
    fun a b h => ntMove_ne h
  have hevenK : ∀ t : Fin (m + 6),
      ntEven (m + 7) ∉ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t
    exact ntInc5_notK (k := m + 5) (by omega)
      (by have ht := t.is_lt; omega) (hjpf t) (ntEven_mem m).2.2
  have hoddK : ∀ t : Fin (m + 6),
      ntOdd (m + 5) ∉ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t
    exact ntInc5_notK (k := m + 5) (by omega)
      (by have ht := t.is_lt; omega) (hjpf t) (ntOdd_mem m).2.2
  have hclosed : ∀ t : Fin (m + 6),
      ∀ x ∈ ntK (m + 7) (t.val + 1) (hjpf t), ∀ y : Equiv.Perm (Fin (m + 7)),
        (ntMove (m + 7) x y ∨ ntMove (m + 7) y x) →
          y ∈ ntK (m + 7) (t.val + 1) (hjpf t) := by
    intro t x hx y h
    have ht := t.is_lt
    exact ntK_closed (by omega) (by omega) (hjpf t) hx h
  refine ntNcl_eq_of_reps (x := fun k : Fin (m + 8) =>
    if h : k.val < m + 6 then hub ⟨k.val, h⟩
    else if _ : k.val = m + 6 then ntEven (m + 7) else ntOdd (m + 5)) ?_ ?_ ?_ ?_
  · intro k
    by_cases hk : k.val < m + 6
    · simp only [dite_eq_left hk]
      exact hsub ⟨k.val, hk⟩ (hhubmem _)
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6]
        exact (ntEven_mem m).1
      · simp only [dite_eq_right hk, dite_eq_right hk6]
        exact (ntOdd_mem m).1
  · intro k
    by_cases hk : k.val < m + 6
    · simp only [dite_eq_left hk]
      exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (hhubmem _).2)
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6]
        exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (ntEven_mem m).2.1)
      · simp only [dite_eq_right hk, dite_eq_right hk6]
        exact (ntNcl_nontrivial_iff hirr).mpr (ntPat_move (ntOdd_mem m).2.1)
  · intro k l hkl h
    have hsign_even : Equiv.Perm.sign (ntEven (m + 7)) = 1 := by
      unfold ntEven
      exact Equiv.Perm.sign_one
    have hsign_odd : Equiv.Perm.sign (ntOdd (m + 5)) = -1 := by
      unfold ntOdd
      apply Equiv.Perm.sign_swap
      intro hcon
      have e2 : m + 5 = m + 5 + 1 := congrArg Fin.val hcon
      omega
    by_cases hk : k.val < m + 6 <;> by_cases hl : l.val < m + 6
    · simp only [dite_eq_left hk, dite_eq_left hl] at h
      set t1 : Fin (m + 6) := ⟨k.val, hk⟩
      set t2 : Fin (m + 6) := ⟨l.val, hl⟩
      have hv1 : t1.val = k.val := rfl
      have hv2 : t2.val = l.val := rfl
      have ht12 : t1 ≠ t2 := by
        intro e
        apply hkl
        have e3 := congrArg Fin.val e
        exact Fin.ext (hv1.symm.trans (e3.trans hv2))
      have hj12 : t1.val + 1 ≠ t2.val + 1 := by
        intro e
        apply ht12
        apply Fin.ext
        omega
      have hdisj := ntK_disjoint (n := m + 7) (j := t1.val + 1) (k := t2.val + 1)
        (by omega) (by have h1 := t1.is_lt; omega) (hjpf t1)
        (by have h2 := t2.is_lt; omega) (hjpf t2) hj12
      have hmem1 : hub t2 ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
        (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
      exact Set.disjoint_left.mp hdisj hmem1 (hhubmem t2)
    · by_cases hl6 : l.val = m + 6
      · simp only [dite_eq_left hk, dite_eq_right hl, dite_eq_left hl6] at h
        set t1 : Fin (m + 6) := ⟨k.val, hk⟩
        have hmemE : ntEven (m + 7) ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
          (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
        exact hevenK t1 hmemE
      · simp only [dite_eq_left hk, dite_eq_right hl, dite_eq_right hl6] at h
        set t1 : Fin (m + 6) := ⟨k.val, hk⟩
        have hmemO : ntOdd (m + 5) ∈ ntK (m + 7) (t1.val + 1) (hjpf t1) :=
          (ntClosed_mem (hclosed t1) h).mp (hhubmem t1)
        exact hoddK t1 hmemO
    · by_cases hk6 : k.val = m + 6
      · simp only [dite_eq_right hk, dite_eq_left hk6, dite_eq_left hl] at h
        set t2 : Fin (m + 6) := ⟨l.val, hl⟩
        have h' : Relation.EqvGen (ntMove (m + 7)) (hub t2) (ntEven (m + 7)) :=
          Relation.EqvGen.symm _ _ h
        have hmemE : ntEven (m + 7) ∈ ntK (m + 7) (t2.val + 1) (hjpf t2) :=
          (ntClosed_mem (hclosed t2) h').mp (hhubmem t2)
        exact hevenK t2 hmemE
      · simp only [dite_eq_right hk, dite_eq_right hk6, dite_eq_left hl] at h
        set t2 : Fin (m + 6) := ⟨l.val, hl⟩
        have h' : Relation.EqvGen (ntMove (m + 7)) (hub t2) (ntOdd (m + 5)) :=
          Relation.EqvGen.symm _ _ h
        have hmemO : ntOdd (m + 5) ∈ ntK (m + 7) (t2.val + 1) (hjpf t2) :=
          (ntClosed_mem (hclosed t2) h').mp (hhubmem t2)
        exact hoddK t2 hmemO
    · by_cases hk6 : k.val = m + 6 <;> by_cases hl6 : l.val = m + 6
      · apply hkl
        apply Fin.ext
        omega
      · simp only [dite_eq_right hk, dite_eq_left hk6, dite_eq_right hl,
          dite_eq_right hl6] at h
        have hs := ntEqvGen_sign h
        rw [hsign_even, hsign_odd] at hs
        exact absurd hs (by decide)
      · simp only [dite_eq_right hk, dite_eq_right hk6, dite_eq_right hl,
          dite_eq_left hl6] at h
        have hs := ntEqvGen_sign h
        rw [hsign_odd, hsign_even] at hs
        exact absurd hs (by decide)
      · apply hkl
        apply Fin.ext
        have hkk := k.is_lt
        have hll := l.is_lt
        omega
  · intro z hzE hcardz
    obtain ⟨y, hy⟩ := (ntNcl_nontrivial_iff hirr).mp hcardz
    have hpat : ntPat (m + 7) z := ntMove_pat hy
    by_cases hex : ∃ t : Fin (m + 6), z ∈ ntK (m + 7) (t.val + 1) (hjpf t)
    · obtain ⟨t, hmem⟩ := hex
      have htk : t.val < m + 8 := by
        have ht := t.is_lt
        omega
      refine ⟨⟨t.val, htk⟩, ?_⟩
      have hlt : (⟨t.val, htk⟩ : Fin (m + 8)).val < m + 6 := t.is_lt
      simp only [dite_eq_left hlt]
      have hteq : (⟨(⟨t.val, htk⟩ : Fin (m + 8)).val, hlt⟩ : Fin (m + 6)) = t :=
        Fin.ext rfl
      rw [hteq]
      exact hhubreach t z hmem
    · have hzG : z ∈ ntG (m + 6) := by
        refine ⟨hzE, hpat, ?_⟩
        intro j hj hmem
        by_cases hj0 : j = 0
        · subst hj0
          rw [ntK_zero_empty hj] at hmem
          exact absurd hmem (Set.notMem_empty z)
        · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
          have hjm : j' < m + 6 := by omega
          refine hex ⟨⟨j', hjm⟩, ?_⟩
          exact hmem
      rcases ntG_two m hzG with h | h
      · have htk : m + 6 < m + 8 := by omega
        refine ⟨⟨m + 6, htk⟩, ?_⟩
        have hval : ((⟨m + 6, htk⟩ : Fin (m + 8)).val) = m + 6 := rfl
        have hnlt : ¬ ((⟨m + 6, htk⟩ : Fin (m + 8)).val < m + 6) := by omega
        simp only [dite_eq_right hnlt]
        exact h
      · have htk : m + 7 < m + 8 := by omega
        refine ⟨⟨m + 7, htk⟩, ?_⟩
        have hval : ((⟨m + 7, htk⟩ : Fin (m + 8)).val) = m + 7 := rfl
        have hnlt : ¬ ((⟨m + 7, htk⟩ : Fin (m + 8)).val < m + 6) := by omega
        have hne6 : ¬ ((⟨m + 7, htk⟩ : Fin (m + 8)).val = m + 6) := by omega
        simp only [dite_eq_right hnlt, dite_eq_right hne6]
        exact h

/-- The class count equals the formula for all `n ≥ 5`. -/
lemma ntCount_eq (k : ℕ) (hk : 5 ≤ k) :
    ntncl (ntMove k) Set.univ = (k ^ 3 + 6 * k ^ 2 - 55 * k + 54) / 6 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 5 := ⟨k - 5, by omega⟩
  have htwo : ∀ t, 6 * ntncl (ntMove (t + 5)) Set.univ =
      (t + 5) ^ 3 + 6 * (t + 5) ^ 2 - 55 * (t + 5) + 54 := by
    intro t
    induction t using Nat.twoStepInduction with
    | zero =>
      have h : 6 * ntncl (ntMove 5) Set.univ =
          5 ^ 3 + 6 * 5 ^ 2 - 55 * 5 + 54 := by
        norm_num [ntSmall5]
      exact h
    | one =>
      have h : 6 * ntncl (ntMove 6) Set.univ =
          6 ^ 3 + 6 * 6 ^ 2 - 55 * 6 + 54 := by
        norm_num [ntSmall6]
      exact h
    | more n ih1 ih2 =>
      have hrec := ntCount_recursion (n + 5)
      have he' : ntncl (ntMove (n + 5 + 2)) (ntE (n + 5 + 1)) = n + 8 :=
        ntE_formula n
      rw [he'] at hrec
      have hrec' : ntncl (ntMove (n + 7)) Set.univ +
          ntncl (ntMove (n + 5)) Set.univ =
          2 * ntncl (ntMove (n + 6)) Set.univ + (n + 8) := hrec
      have hgoal : 6 * ntncl (ntMove (n + 7)) Set.univ =
          (n + 7) ^ 3 + 6 * (n + 7) ^ 2 - 55 * (n + 7) + 54 := by
        have ih1Z : (6 : ℤ) * ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) =
            ((((n + 5) ^ 3 + 6 * (n + 5) ^ 2 - 55 * (n + 5) + 54 : ℕ)) : ℤ) := by
          exact_mod_cast ih1
        have ih2Z : (6 : ℤ) * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ) =
            ((((n + 6) ^ 3 + 6 * (n + 6) ^ 2 - 55 * (n + 6) + 54 : ℕ)) : ℤ) := by
          exact_mod_cast ih2
        have hrecZ : (6 : ℤ) * ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) =
            2 * (6 * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ)) -
              6 * ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) +
              6 * ((((n : ℕ) + 8 : ℕ)) : ℤ) := by
          have hZ : ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) +
              ((ntncl (ntMove (n + 5)) Set.univ : ℕ) : ℤ) =
              2 * ((ntncl (ntMove (n + 6)) Set.univ : ℕ) : ℤ) +
              ((((n : ℕ) + 8 : ℕ)) : ℤ) := by
            exact_mod_cast hrec'
          linarith
        rw [ih1Z, ih2Z] at hrecZ
        have hcast8 : ((((n : ℕ) + 8 : ℕ)) : ℤ) = ((n : ℕ) : ℤ) + 8 := by
          push_cast
          ring
        rw [hcast8] at hrecZ
        have h5 := ntNum_cast (n + 5) (by omega)
        have h6 := ntNum_cast (n + 6) (by omega)
        have h7 := ntNum_cast (n + 7) (by omega)
        rw [h5, h6] at hrecZ
        have hfin : (6 : ℤ) * ((ntncl (ntMove (n + 7)) Set.univ : ℕ) : ℤ) =
            ((((n + 7) ^ 3 + 6 * (n + 7) ^ 2 - 55 * (n + 7) + 54 : ℕ)) : ℤ) := by
          rw [hrecZ, h7]
          exact ntPoly_step n
        exact_mod_cast hfin
      exact hgoal
  have hP := htwo t
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/-- For n ≥ 7, the number of nontrivial equivalence classes of S_n under the {1234,
3412}-equivalence is (n^3 + 6n^2 - 55n + 54)/6, conjectured by Ma and given by sequence A330395.
Source: Quinn Perian, Bella Xu, and Alexander Lu Zhang, "Counting the Nontrivial Equivalence Classes
of Sn Under {1234,3412}-Pattern-Replacement", Journal of Integer Sequences 23 (2020), Article
20.10.2, Theorem `thm:nontrivial`, lines 172-175,
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Zhang/zhang6.tex>.

Proof: Decompose the exceptional set into swap classes and a generic part. Kernel-checked
finite certificates handle the `S₅`/`S₆` classes, `S₇` reachability, and the `S₈` deletion
boundary. Point insertion then gives the recurrence, whose solution is the displayed polynomial.

Proves `Wanted` entry `card_nontrivial_1234_3412_classes`.
-/
theorem card_nontrivial_1234_3412_classes :
    ∀ (n : ℕ), 7 ≤ n →
      let OneMove : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop :=
        fun σ τ => ∃ i1 i2 i3 i4 : Fin n,
          i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
            σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
            τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
            ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j;
      Nat.card { C : Set (Equiv.Perm (Fin n)) //
          ∃ σ, C = { τ | Relation.EqvGen OneMove σ τ } ∧ 1 < Nat.card ↥C } =
        (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 := by
  intro n hn
  have hequiv : Nat.card { C : Set (Equiv.Perm (Fin n)) //
        ∃ σ, C = { τ | Relation.EqvGen (ntMove n) σ τ } ∧ 1 < Nat.card ↥C } =
      ntncl (ntMove n) Set.univ :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun C => by
      constructor
      · rintro ⟨σ, hC, hcard⟩
        exact ⟨σ, Set.mem_univ σ, hC, hcard⟩
      · rintro ⟨σ, -, hC, hcard⟩
        exact ⟨σ, hC, hcard⟩))
  have hfin : ntncl (ntMove n) Set.univ =
      (n ^ 3 + 6 * n ^ 2 - 55 * n + 54) / 6 :=
    ntCount_eq n (by omega)
  exact hequiv.trans hfin

end MetaMathlibExt
