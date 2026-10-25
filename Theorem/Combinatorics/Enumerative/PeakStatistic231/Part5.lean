/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PeakStatistic231.lean -/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Finset.Fin
import Def.Combinatorics.Enumerative.PeakStatistic231.Part5


section

namespace MetaMathlibExt

namespace Peak231

theorem rightPerm_val {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) (j : Fin b) :
    (rightPerm σ hAv hmax j).val =
      (σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a := by
  have h : rightPerm σ hAv hmax j =
      (⟨(σ ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩).val - a,
        rightPerm_bound σ hAv hmax j ⟨a + 1 + j.val, by have hj := j.isLt; omega⟩
          rfl⟩ : Fin b) := by
    simp only [rightPerm, Equiv.ofBijective_apply]
  have hcon := congrArg Fin.val h
  exact hcon

theorem exists_joinMax_eq {a b : ℕ} (σ : Equiv.Perm (Fin (a + b + 1)))
    (hAv : Avoids231 σ) (hmax : (σ.symm (Fin.last (a + b))).val = a) :
    ∃ α β, joinMax α β = σ := by
  refine ⟨leftPerm σ hAv hmax, rightPerm σ hAv hmax, ?_⟩
  apply Equiv.ext
  intro p
  apply Fin.ext
  by_cases hlt : p.val < a
  · have e1 := joinMax_apply_lt (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
      (i := p) hlt
    rw [e1]
    have e2 := leftPerm_val σ hAv hmax ⟨p.val, hlt⟩
    rw [e2]
  · by_cases heq : p.val = a
    · have e1 := joinMax_val_of_eq (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
        (p := p) heq
      rw [e1]
      have hsymm : σ.symm (Fin.last (a + b)) = (⟨a, by omega⟩ : Fin (a + b + 1)) :=
        Fin.ext hmax
      have htop : σ (⟨a, by omega⟩ : Fin (a + b + 1)) = Fin.last (a + b) := by
        have h := Equiv.apply_symm_apply σ (Fin.last (a + b))
        rwa [hsymm] at h
      have hp : p = ⟨a, by omega⟩ := Fin.ext heq
      rw [hp, htop, Fin.val_last]
    · have hgt : a < p.val := by omega
      have e1 := joinMax_apply_gt (leftPerm σ hAv hmax) (rightPerm σ hAv hmax)
        (i := p) hgt
      rw [e1]
      have e2 := rightPerm_val σ hAv hmax
        ⟨p.val - a - 1, by have hp := p.isLt; omega⟩
      rw [e2]
      have hpp : (⟨a + 1 + (⟨p.val - a - 1, by have hp := p.isLt; omega⟩ : Fin b).val,
          by have hp := p.isLt; omega⟩ : Fin (a + b + 1)) = p := by
        apply Fin.ext
        change a + 1 + (p.val - a - 1) = p.val
        omega
      rw [hpp]
      have hge := joinMax_le_of_avoids (l := p) σ hAv hmax hgt
      omega

-- N7
theorem card_fiber_joinMax {a b n k : ℕ} (hab : a + b = n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
      ((Avoids231 σ ∧ peakCount σ = k) ∧ (σ.symm (Fin.last n)).val = a))).card =
    (((Finset.univ.filter (fun α : Equiv.Perm (Fin a) => Avoids231 α)) ×ˢ
      (Finset.univ.filter (fun β : Equiv.Perm (Fin b) => Avoids231 β))).filter
      (fun p =>
        peakCount p.1 + peakCount p.2 + (if a = 0 ∨ b = 0 then 0 else 1) = k)).card := by
  subst hab
  symm
  refine Finset.card_bij (fun (p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) _ =>
    joinMax p.1 p.2) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨hα, hβ⟩, hpk⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (avoids231_joinMax_iff p.1 p.2).mpr ⟨hα, hβ⟩
    · rw [peakCount_joinMax]
      exact hpk
    · have h := joinMax_symm_last p.1 p.2
      have hv : ((joinMax p.1 p.2).symm (Fin.last (a + b))).val = a :=
        congrArg Fin.val h
      exact hv
  · intro p1 hp1 p2 hp2 heq
    have heq' : joinMax p1.1 p1.2 = joinMax p2.1 p2.2 := heq
    have h := joinMax_inj heq'
    exact Prod.ext h.1 h.2
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    obtain ⟨⟨hAv, hpk⟩, hmax⟩ := hσ
    obtain ⟨α, β, rfl⟩ := exists_joinMax_eq σ hAv hmax
    have hAB := (avoids231_joinMax_iff α β).mp hAv
    refine ⟨(α, β), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    refine ⟨hAB, ?_⟩
    rw [peakCount_joinMax α β] at hpk
    exact hpk

theorem avoidCount_succ (n k : ℕ) :
    avoidCount (n + 1) k = peakRec avoidCount n k := by
  have hmaps : Set.MapsTo (fun σ : Equiv.Perm (Fin (n + 1)) => (σ.symm (Fin.last n)).val)
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
        Avoids231 σ ∧ peakCount σ = k)) : Set (Equiv.Perm (Fin (n + 1))))
      (Finset.range n.succ) := by
    intro σ _
    apply Finset.mem_coe.mpr
    exact Finset.mem_range.mpr (σ.symm (Fin.last n)).isLt
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps
  have hav : ∀ (m j : ℕ),
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ)).filter
        (fun x => peakCount x = j)).card = avoidCount m j := by
    intro m j
    have hfl : (Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ)).filter
        (fun x => peakCount x = j) =
        Finset.univ.filter (fun σ : Equiv.Perm (Fin m) => Avoids231 σ ∧ peakCount σ = j) := by
      rw [Finset.filter_filter]
    rw [hfl]
    rfl
  have hstep : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
        Avoids231 σ ∧ peakCount σ = k)).filter
        (fun σ => (σ.symm (Fin.last n)).val = q.1)).card =
      (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
        else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) := by
    intro q hq
    have hmem : q.1 + q.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
    have hN7 := card_fiber_joinMax (a := q.1) (b := q.2) (n := n) (k := k) hmem
    have hbridge : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
          Avoids231 σ ∧ peakCount σ = k)).filter
          (fun σ => (σ.symm (Fin.last n)).val = q.1)).card =
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) =>
          ((Avoids231 σ ∧ peakCount σ = k) ∧ (σ.symm (Fin.last n)).val = q.1))).card := by
      apply congrArg Finset.card
      rw [Finset.filter_filter]
    rw [hbridge, hN7]
    by_cases he : q.1 = 0 ∨ q.2 = 0
    · have hif : (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
          else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) =
          peakConv avoidCount q.1 q.2 k := ite_eq_left he
      rw [hif]
      have hoff : (if q.1 = 0 ∨ q.2 = 0 then (0:ℕ) else 1) = 0 := ite_eq_left he
      have hfc : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = k)) =
          (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 = k)) := by
        apply Finset.filter_congr
        intro p _
        simp only [hoff, add_zero]
      rw [hfc]
      have hN8 := card_filter_add_eq_sum_antidiagonal
        (Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α))
        (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))
        peakCount peakCount k
      rw [hN8]
      unfold peakConv
      apply Finset.sum_congr rfl
      intro r hr
      rw [hav q.1 r.1, hav q.2 r.2]
    · have hif : (if q.1 = 0 ∨ q.2 = 0 then peakConv avoidCount q.1 q.2 k
          else (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1))) =
          (if k = 0 then 0 else peakConv avoidCount q.1 q.2 (k - 1)) :=
        ite_eq_right he
      rw [hif]
      have hoff : (if q.1 = 0 ∨ q.2 = 0 then (0:ℕ) else 1) = 1 := ite_eq_right he
      by_cases hk : k = 0
      · subst hk
        have hempty : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = 0)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p _
          omega
        rw [hempty, Finset.card_empty]
        exact (ite_eq_left rfl).symm
      · have hkif : (if k = 0 then (0:ℕ) else peakConv avoidCount q.1 q.2 (k - 1)) =
            peakConv avoidCount q.1 q.2 (k - 1) := ite_eq_right hk
        rw [hkif]
        have hfc : (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 +
              (if q.1 = 0 ∨ q.2 = 0 then 0 else 1) = k)) =
          (((Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α)) ×ˢ
            (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))).filter
            (fun p => peakCount p.1 + peakCount p.2 = k - 1)) := by
          apply Finset.filter_congr
          intro p _
          simp only [hoff]
          constructor <;> intro h <;> omega
        rw [hfc]
        have hN8 := card_filter_add_eq_sum_antidiagonal
          (Finset.univ.filter (fun α : Equiv.Perm (Fin q.1) => Avoids231 α))
          (Finset.univ.filter (fun β : Equiv.Perm (Fin q.2) => Avoids231 β))
          peakCount peakCount (k - 1)
        rw [hN8]
        unfold peakConv
        apply Finset.sum_congr rfl
        intro r hr
        rw [hav q.1 r.1, hav q.2 r.2]
  conv_lhs => unfold avoidCount
  rw [hfib, sum_range_fiber_eq_sum_antidiagonal]
  unfold peakRec
  apply Finset.sum_congr rfl
  intro q hq
  exact hstep q hq

-- N14
theorem avoidCount_eq_peakT (n k : ℕ) : avoidCount n k = peakT n k := by
  revert k
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k
    by_cases hn : n = 0
    · subst hn
      have hA : ∀ σ : Equiv.Perm (Fin 0), Avoids231 σ := by
        intro σ i j l _ _ _
        exact Fin.elim0 i
      have hpc : ∀ σ : Equiv.Perm (Fin 0), peakCount σ = 0 := by
        intro σ
        unfold peakCount
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact Fin.elim0 x
      have hset : (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin 0) => Avoids231 σ ∧ peakCount σ = k)) =
          (if k = 0 then Finset.univ else ∅) := by
        ext σ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hk : k = 0
        · subst hk
          simp only [ite_true, Finset.mem_univ]
          rw [hpc σ]
          exact iff_true_intro ⟨hA σ, rfl⟩
        · have hk0 : peakCount σ ≠ k := by rw [hpc σ]; omega
          simp only [hk, ite_false, Finset.notMem_empty]
          exact iff_false_intro (fun h => hk0 h.2)
      have hcard : avoidCount 0 k = (if k = 0 then 1 else 0) := by
        unfold avoidCount
        rw [hset]
        by_cases hk : k = 0
        · subst hk
          simp only [ite_true, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, Nat.factorial_zero]
        · simp only [hk, ite_false, Finset.card_empty]
      have hT : peakT 0 k = (if k = 0 then 1 else 0) := by
        unfold peakT
        by_cases hk : k = 0
        · subst hk
          simp
        · have hC : Nat.choose (0 - 1) (2 * k) = 0 := by
            have h1 : (0:ℕ) - 1 = 0 := by omega
            rw [h1]
            apply Nat.choose_eq_zero_of_lt
            omega
          rw [hC]
          simp only [mul_zero, zero_mul, hk, ite_false]
      rw [hcard, hT]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hEq : ∀ a : ℕ, a ≤ m → ∀ j : ℕ, avoidCount a j = peakT a j := by
        intro a ha j
        exact ih a (by omega) j
      rw [avoidCount_succ, peakT_succ]
      unfold peakRec peakConv
      apply Finset.sum_congr rfl
      intro q hq
      have hmem : q.1 + q.2 = m :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hq
      have ha1 : q.1 ≤ m := by omega
      have ha2 : q.2 ≤ m := by omega
      by_cases he : q.1 = 0 ∨ q.2 = 0
      · simp only [he, ite_true]
        apply Finset.sum_congr rfl
        intro p _
        rw [hEq q.1 ha1, hEq q.2 ha2]
      · simp only [he, ite_false]
        by_cases hk : k = 0
        · simp only [hk, ite_true]
        · simp only [hk, ite_false]
          apply Finset.sum_congr rfl
          intro p _
          rw [hEq q.1 ha1, hEq q.2 ha2]

end Peak231

-- N15
/--
The number of 231-avoiding permutations of length `n` with exactly `k` peaks has the stated
closed form.
Source: Lara Pudwell, Jacob Roth, and Teresa Wheeland, "Distributions of Statistics
over Pattern-Avoiding Permutations", Journal of Integer Sequences 22 (2019),
Article 19.2.6, Theorem `T:pk231`, line 228,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Pudwell/pudwell6.tex>.

Proves `Wanted` entry `card_permutations_avoiding_231_with_peak_count`.
-/
theorem card_permutations_avoiding_231_with_peak_count
    (n k : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
      2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * Nat.choose (2 * k) k /
        (k + 1) := by
  have _ : 1 ≤ n := hn
  have hCat : (k + 1) * catalan k = Nat.choose (2 * k) k := by
    rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
  have hRHS : 2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) *
      Nat.choose (2 * k) k / (k + 1) =
      2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k := by
    have hC : Nat.choose (2 * k) k = (k + 1) * catalan k := hCat.symm
    conv_lhs => rw [hC]
    have hring : 2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) *
        ((k + 1) * catalan k) =
        (2 ^ (n - 2 * k - 1) * Nat.choose (n - 1) (2 * k) * catalan k) *
        (k + 1) := by ring
    rw [hring, Nat.mul_div_cancel _ (Nat.succ_pos k)]
  have hBridge : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (∀ i j l : Fin n, i < j → j < l → ¬ (σ l < σ i ∧ σ i < σ j)) ∧
      (Finset.univ.filter (fun i : Fin n =>
        ∃ iPrev iNext : Fin n,
          iPrev.val + 1 = i.val ∧ i.val + 1 = iNext.val ∧
          σ iPrev < σ i ∧ σ iNext < σ i)).card = k)).card =
      Peak231.avoidCount n k := rfl
  rw [hBridge, Peak231.avoidCount_eq_peakT]
  unfold Peak231.peakT
  exact hRHS.symm

end MetaMathlibExt
end
