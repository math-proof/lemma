/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/TwoDistantPolarized.lean -/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.List.Indexes
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.TwoDistantPolarized.Part9


namespace MetaMathlibExt.TwoDistantPolarized

open List

theorem invB_pairwise {n : ℕ} (p : Nat.Partition n) : (invB p).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem invB_sum {n : ℕ} (p : Nat.Partition n) (hnd : p.parts.Nodup)
    (hpol : ∀ e ∈ p.parts, e % 2 = 0 → 2 * (p.parts.filter (fun i => i % 2 = 1)).card < e) :
    (invB p).sum + (invB p).length ^ 2 = n := by
  have hPl : fromB (toB (Pl p)) = Pl p := fromB_toB (Pl p) (Pl_gap p hnd) (Pl_pos p)
  have hQl : Qof (Pl p).length (toBoff (Pl p).length (Ql p)) = Ql p :=
    Qof_toBoff (Pl p).length (Ql p) (Ql_gap p hnd) (Ql_bound p hpol)
  have e3 : (Pl p).sum = (toB (Pl p)).sum + (Pl p).length ^ 2 := by
    conv_lhs => rw [← hPl]
    rw [sum_fromB, length_toB]
  have e4 : (Ql p).sum
      = (toBoff (Pl p).length (Ql p)).sum +
          (2 * (Pl p).length * (Ql p).length + (Ql p).length ^ 2) := by
    conv_lhs => rw [← hQl]
    rw [sum_Qof, length_toBoff]
  have e5 : (Pl p).sum + (Ql p).sum = n := by
    have := oddm_add_evenm p
    have hh : (oddm p).sum + (evenm p).sum = n := by
      rw [← Multiset.sum_add, this, p.parts_sum]
    rw [Pl, Ql, sortsum, sortsum]; exact hh
  have e1 : (invB p).sum = (toB (Pl p)).sum + (toBoff (Pl p).length (Ql p)).sum := by
    rw [invB, sortsum, Multiset.sum_add, Multiset.sum_coe, Multiset.sum_coe]
  have e2 : (invB p).length = (Pl p).length + (Ql p).length := by
    rw [invB, Multiset.length_sort, Multiset.card_add, Multiset.coe_card, Multiset.coe_card,
      length_toB, length_toBoff]
  rw [e1, e2]
  have hexp : (toB (Pl p)).sum + (toBoff (Pl p).length (Ql p)).sum
        + ((Pl p).length + (Ql p).length) ^ 2
      = ((toB (Pl p)).sum + (Pl p).length ^ 2)
        + ((toBoff (Pl p).length (Ql p)).sum
          + (2 * (Pl p).length * (Ql p).length + (Ql p).length ^ 2)) := by ring
  rw [hexp, ← e3, ← e4]; exact e5

theorem polyParts_evenfilter (b : List ℕ) :
    (polyParts b).filter (fun a => decide (a % 2 = 0)) = Qof (evenP b).length (oddP b) := by
  rw [polyParts, List.filter_append]
  have h1 : (fromB (evenP b)).filter (fun a => decide (a % 2 = 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr; intro a ha; simp only [decide_eq_true_eq]
    have := fromB_odd _ (evenP_even b) a ha; omega
  have h2 : (Qof (evenP b).length (oddP b)).filter (fun a => decide (a % 2 = 0))
      = Qof (evenP b).length (oddP b) := by
    apply List.filter_eq_self.mpr; intro a ha; simp only [decide_eq_true_eq]
    exact Qof_even _ _ (oddP_odd b) a ha
  rw [h1, h2, List.nil_append]

theorem toB_even (L : List ℕ) (hodd : ∀ x ∈ L, x % 2 = 1)
    (hpair : L.Pairwise (fun a c => a + 2 ≤ c)) (hpos : ∀ x ∈ L, 0 < x) :
    ∀ x ∈ toB L, x % 2 = 0 := by
  intro x hx; rw [List.mem_iff_getElem] at hx; obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < L.length := by simpa using hi
  have hb := staircase_bound L hpair hpos i hi'
  have hpar := hodd L[i] (List.getElem_mem hi')
  simp only [toB, getElem_mapIdx]; omega

theorem Pl_val {n : ℕ} (q : Nat.Partition n) (b : List ℕ) (hb : b.Pairwise (· ≤ ·))
    (h : q.parts = ↑(polyParts b)) : Pl q = fromB (evenP b) := by
  rw [Pl, oddm, h, Multiset.filter_coe, polyParts_oddfilter]
  exact sort_coe_self _ ((fromB_pairwise _ (evenP_pairwise b hb)).imp (fun hh => by omega))

theorem Ql_val {n : ℕ} (q : Nat.Partition n) (b : List ℕ) (hb : b.Pairwise (· ≤ ·))
    (h : q.parts = ↑(polyParts b)) : Ql q = Qof (evenP b).length (oddP b) := by
  rw [Ql, evenm, h, Multiset.filter_coe, polyParts_evenfilter]
  exact sort_coe_self _ ((Qof_pairwise _ _ (oddP_pairwise b hb)).imp (fun hh => by omega))

theorem invB_of_parts {n : ℕ} (q : Nat.Partition n) (b : List ℕ) (hb : b.Pairwise (· ≤ ·))
    (h : q.parts = ↑(polyParts b)) : invB q = b := by
  rw [invB, Pl_val q b hb h, Ql_val q b hb h, length_fromB, toB_fromB, toBoff_Qof,
    Multiset.coe_add, Multiset.coe_eq_coe.mpr (split_perm b)]
  exact sort_coe_self b hb

theorem toBoff_pairwise (j : ℕ) (Q : List ℕ) (hpair : Q.Pairwise (fun a c => a + 2 ≤ c))
    (h0 : ∀ (hpos : 0 < Q.length), 2 * j + 1 ≤ Q[0]'hpos) : (toBoff j Q).Pairwise (· ≤ ·) := by
  rw [pairwise_iff_getElem]
  intro s t hs ht hst
  have hbs := offset_staircase_bound j Q hpair h0 s (by simpa using hs)
  have hbt := offset_staircase_bound j Q hpair h0 t (by simpa using ht)
  have hc := cumul Q hpair t (by simpa using ht) s (by omega)
  simp only [toBoff, getElem_mapIdx]; omega

theorem evenP_invB {n : ℕ} (μ : Nat.Partition n) (hnd : μ.parts.Nodup)
    (hpol : ∀ e ∈ μ.parts, e % 2 = 0 → 2 * (μ.parts.filter (fun i => i % 2 = 1)).card < e) :
    evenP (invB μ) = toB (Pl μ) := by
  apply sorted_eq_of_coe_eq
  · exact evenP_pairwise (invB μ) (invB_pairwise μ)
  · exact toB_pairwise (Pl μ) (Pl_gap μ hnd) (Pl_pos μ)
  · have hself : (↑(toB (Pl μ)) : Multiset ℕ).filter (fun x => x % 2 = 0) = ↑(toB (Pl μ)) := by
      rw [Multiset.filter_eq_self]; intro a ha
      exact toB_even (Pl μ) (Pl_odd μ) (Pl_gap μ hnd) (Pl_pos μ) a (by simpa using ha)
    have hnil : (↑(toBoff (Pl μ).length (Ql μ)) : Multiset ℕ).filter (fun x => x % 2 = 0) = 0 := by
      rw [Multiset.filter_eq_nil]; intro a ha
      have := toBoff_odd (Pl μ).length (Ql μ) (Ql_even μ)
        (offset_staircase_bound _ _ (Ql_gap μ hnd) (Ql_bound μ hpol)) a (by simpa using ha)
      omega
    rw [evenP, ← Multiset.filter_coe, invB, Multiset.sort_eq, Multiset.filter_add, hself, hnil,
      add_zero]

theorem oddP_invB {n : ℕ} (μ : Nat.Partition n) (hnd : μ.parts.Nodup)
    (hpol : ∀ e ∈ μ.parts, e % 2 = 0 → 2 * (μ.parts.filter (fun i => i % 2 = 1)).card < e) :
    oddP (invB μ) = toBoff (Pl μ).length (Ql μ) := by
  apply sorted_eq_of_coe_eq
  · exact oddP_pairwise (invB μ) (invB_pairwise μ)
  · exact toBoff_pairwise (Pl μ).length (Ql μ) (Ql_gap μ hnd) (Ql_bound μ hpol)
  · have hpred : (fun x => !decide (x % 2 = 0)) = (fun x : ℕ => decide (x % 2 ≠ 0)) := by
      funext x; rw [decide_not]
    have hnil : (↑(toB (Pl μ)) : Multiset ℕ).filter (fun x => x % 2 ≠ 0) = 0 := by
      rw [Multiset.filter_eq_nil]; intro a ha
      have := toB_even (Pl μ) (Pl_odd μ) (Pl_gap μ hnd) (Pl_pos μ) a (by simpa using ha); omega
    have hself : (↑(toBoff (Pl μ).length (Ql μ)) : Multiset ℕ).filter (fun x => x % 2 ≠ 0)
        = ↑(toBoff (Pl μ).length (Ql μ)) := by
      rw [Multiset.filter_eq_self]; intro a ha
      have := toBoff_odd (Pl μ).length (Ql μ) (Ql_even μ)
        (offset_staircase_bound _ _ (Ql_gap μ hnd) (Ql_bound μ hpol)) a (by simpa using ha); omega
    rw [oddP, hpred, ← Multiset.filter_coe, invB, Multiset.sort_eq, Multiset.filter_add, hnil,
      hself, zero_add]

theorem polyParts_invB {n : ℕ} (μ : Nat.Partition n) (hnd : μ.parts.Nodup)
    (hpol : ∀ e ∈ μ.parts, e % 2 = 0 → 2 * (μ.parts.filter (fun i => i % 2 = 1)).card < e) :
    (↑(polyParts (invB μ)) : Multiset ℕ) = μ.parts := by
  have hQ : Qof (Pl μ).length (toBoff (Pl μ).length (Ql μ)) = Ql μ :=
    Qof_toBoff (Pl μ).length (Ql μ) (Ql_gap μ hnd) (Ql_bound μ hpol)
  have hP : fromB (toB (Pl μ)) = Pl μ := fromB_toB (Pl μ) (Pl_gap μ hnd) (Pl_pos μ)
  rw [polyParts, evenP_invB μ hnd hpol, oddP_invB μ hnd hpol, hP, length_toB, hQ,
    ← Multiset.coe_add, Pl, Ql]
  simp only [Multiset.sort_eq]
  rw [oddm_add_evenm]

end MetaMathlibExt.TwoDistantPolarized
