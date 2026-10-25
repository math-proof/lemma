/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/CrankGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Non-negative crank generating function (Andrews–Newman / Uncu):
the number of partitions of `N` with crank `≥ 0` equals the alternating
sum of partition numbers at triangular offsets.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.GetD
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.CrankGeneratingFunction.Part5


namespace MetaMathlibExt

namespace CrankNonneg

theorem crkMkPartition_parts (L a : ℕ) (l : List ℕ)
    (hpos : ∀ x ∈ l, 1 ≤ x) (hsum : a + l.sum = L) :
    (crkMkPartition L a l hpos hsum).parts = ((l : Multiset ℕ) + Multiset.replicate a 1) :=
  rfl

theorem crk_filter_threshold {n : ℕ} (P : Nat.Partition n) (t : ℕ) (ht : 1 ≤ t) :
    (P.parts.filter (fun x => t < x)).card =
    ((nonOneParts P).filter (fun x => t < x)).length := by
  rw [crk_parts_eq_nonOne_add P, Multiset.filter_add, Multiset.card_add]
  have hrep : (Multiset.replicate (Multiset.count 1 P.parts) 1).filter
      (fun x => t < x) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro x hx
    rw [Multiset.mem_replicate] at hx
    obtain ⟨-, rfl⟩ := hx
    omega
  rw [hrep, Multiset.card_zero, Nat.add_zero, Multiset.filter_coe, Multiset.coe_card]

/-! ## Threshold lemmas for weakly decreasing lists -/

theorem crk_filter_split {l l₁ l₂ : List ℕ} (t : ℕ)
    (h : l = l₁ ++ l₂) (h₁ : ∀ x ∈ l₁, t < x) (h₂ : ∀ x ∈ l₂, x ≤ t) :
    (l.filter (fun x => decide (t < x))).length = l₁.length := by
  rw [h, List.filter_append,
    List.filter_eq_self.mpr (fun a ha => by simpa using h₁ a ha),
    List.filter_eq_nil_iff.mpr (fun a ha hcon => by
      have hlt : t < a := of_decide_eq_true hcon
      have hle := h₂ a ha
      omega),
    List.append_nil]

theorem crk_sorted_filter_spec (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) (t : ℕ) :
    (l.filter (fun x => decide (t < x))).length ≤ l.length ∧
    (∀ x ∈ List.take (l.filter (fun x => decide (t < x))).length l, t < x) ∧
    (∀ x ∈ List.drop (l.filter (fun x => decide (t < x))).length l, x ≤ t) := by
  have hempty_of_le : ∀ (hd : ℕ) (tl : List ℕ),
      (∀ y ∈ tl, hd ≥ y) → hd ≤ t →
      ((hd :: tl).filter (fun x => decide (t < x))) = [] := by
    intro hd tl hhead hle
    rw [List.filter_eq_nil_iff]
    intro y hy hcon
    have hlt : t < y := of_decide_eq_true hcon
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · omega
    · have hyhd := hhead y hy
      omega
  have htake : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) →
      ∀ x ∈ List.take (l.filter (fun x => decide (t < x))).length l, t < x := by
    intro l
    induction l with
    | nil =>
      intro _ x hx
      simp at hx
    | cons hd tl ih =>
      intro hl x hx
      rw [List.pairwise_cons] at hl
      obtain ⟨hhead, htail⟩ := hl
      by_cases hhd : t < hd
      · have hfil : ((hd :: tl).filter (fun x => decide (t < x))).length =
            (tl.filter (fun x => decide (t < x))).length + 1 := by
          rw [List.filter_cons_of_pos (by simpa using hhd), List.length_cons]
        rw [hfil, List.take_succ_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hhd
        · exact ih htail x hx
      · have hle : hd ≤ t := le_of_not_gt hhd
        have hempty := hempty_of_le hd tl hhead hle
        have hb0 : ((hd :: tl).filter (fun x => decide (t < x))).length = 0 :=
          List.length_eq_zero_iff.mpr hempty
        rw [hb0] at hx
        simp at hx
  have hdrop : ∀ (l : List ℕ), l.Pairwise (· ≥ ·) →
      ∀ x ∈ List.drop (l.filter (fun x => decide (t < x))).length l, x ≤ t := by
    intro l
    induction l with
    | nil =>
      intro _ x hx
      simp at hx
    | cons hd tl ih =>
      intro hl x hx
      rw [List.pairwise_cons] at hl
      obtain ⟨hhead, htail⟩ := hl
      by_cases hhd : t < hd
      · have hfil : ((hd :: tl).filter (fun x => decide (t < x))).length =
            (tl.filter (fun x => decide (t < x))).length + 1 := by
          rw [List.filter_cons_of_pos (by simpa using hhd), List.length_cons]
        have hdrop : List.drop
            ((tl.filter (fun x => decide (t < x))).length + 1) (hd :: tl) =
            List.drop (tl.filter (fun x => decide (t < x))).length tl :=
          rfl
        rw [hfil, hdrop] at hx
        exact ih htail x hx
      · have hle : hd ≤ t := le_of_not_gt hhd
        have hempty := hempty_of_le hd tl hhead hle
        have hb0 : ((hd :: tl).filter (fun x => decide (t < x))).length = 0 :=
          List.length_eq_zero_iff.mpr hempty
        rw [hb0, List.drop_zero, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hle
        · have hle2 : x ≤ hd := hhead x hx
          omega
  exact ⟨List.length_filter_le _ _, htake l hl, hdrop l hl⟩

theorem crk_mem_filter_iff (l : List ℕ) (hl : l.Pairwise (· ≥ ·)) (t n : ℕ)
    (h : n < l.length) :
    n + 1 ≤ (l.filter (fun x => decide (t < x))).length ↔ t < l[n] := by
  have hspec := crk_sorted_filter_spec l hl t
  set b := (l.filter (fun x => decide (t < x))).length
  constructor
  · intro hle
    have hblen : n < (List.take b l).length := by
      rw [List.length_take]
      omega
    have hmem := List.getElem_mem hblen
    have hlt := hspec.2.1 _ hmem
    rw [List.getElem_take] at hlt
    exact hlt
  · intro hlt
    by_contra hcon
    have hbn : b ≤ n := by omega
    have hlen : n - b < (List.drop b l).length := by
      rw [List.length_drop]
      omega
    have hmem := List.getElem_mem hlen
    have hle := hspec.2.2 _ hmem
    rw [List.getElem_drop] at hle
    simp only [Nat.add_sub_cancel' hbn] at hle
    exact (not_lt.mpr hle) hlt

/-! ## Forward list map -/

theorem crk_sum_map_succ (t : List ℕ) :
    (t.map (· + 1)).sum = t.sum + t.length := by
  induction t with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem crk_phi_sorted (a : ℕ) (l : List ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hlen : a < l.length) :
    (phiList a l).Pairwise (· ≥ ·) := by
  have hpre : ((List.take a l).map (· + 1)).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact (hl.sublist (List.take_sublist a l)).imp (fun h => by omega)
  have hsuf : (List.drop (a + 1) l).Pairwise (· ≥ ·) :=
    hl.sublist (List.drop_sublist (a + 1) l)
  have hacross : ∀ x ∈ (List.take a l).map (· + 1),
      ∀ y ∈ List.drop (a + 1) l, x ≥ y := by
    intro x hx y hy
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_iff_getElem] at hu hy
    obtain ⟨i, hi, hui⟩ := hu
    obtain ⟨j, hj, hyj⟩ := hy
    rw [List.getElem_take] at hui
    rw [List.getElem_drop] at hyj
    have hi_len : i < l.length := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hj_len : (a + 1) + j < l.length := by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega
    have hia : i < a := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hle := (List.pairwise_iff_getElem.mp hl) i ((a + 1) + j) hi_len hj_len
      (by omega)
    omega
  rw [phiList, List.pairwise_append]
  exact ⟨hpre, hsuf, hacross⟩

theorem crk_phi_ge_two (a : ℕ) (l : List ℕ)
    (h2 : ∀ x ∈ l, 2 ≤ x) :
    ∀ x ∈ phiList a l, 2 ≤ x := by
  intro x hx
  rw [phiList, List.mem_append] at hx
  rcases hx with hx | hx
  · rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_iff_getElem] at hu
    obtain ⟨i, hi, hui⟩ := hu
    rw [List.getElem_take] at hui
    have hii : i < l.length := by
      have h3 := hi
      rw [List.length_take] at h3
      omega
    have hu2 : 2 ≤ u := hui ▸ h2 _ (List.getElem_mem hii)
    omega
  · rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, hyj⟩ := hx
    rw [List.getElem_drop] at hyj
    rw [← hyj]
    exact h2 _ (List.getElem_mem (by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega))

theorem crk_phi_sum (a : ℕ) (l : List ℕ)
    (hlen : a < l.length) :
    phiPivot a l + (phiList a l).sum = a + l.sum := by
  have hpiv : phiPivot a l = l[a]'hlen := List.getD_eq_getElem _ _ hlen
  have hdrop : List.drop a l = l[a]'hlen :: List.drop (a + 1) l :=
    List.drop_eq_getElem_cons hlen
  have htsum : (List.take a l).sum + (List.drop a l).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hmap : ((List.take a l).map (· + 1)).sum = (List.take a l).sum + a := by
    rw [crk_sum_map_succ]
    have hlen2 : (List.take a l).length = a := by
      rw [List.length_take, Nat.min_eq_left (le_of_lt hlen)]
    rw [hlen2]
  rw [phiList, hpiv, List.sum_append, hmap]
  rw [hdrop, List.sum_cons] at htsum
  omega

theorem crk_phi_filter (a : ℕ) (l : List ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hlen : a < l.length) :
    ((phiList a l).filter (fun x => decide (phiPivot a l < x))).length = a := by
  have hpiv : phiPivot a l = l[a]'hlen := List.getD_eq_getElem _ _ hlen
  have hsplit : phiList a l =
      (List.take a l).map (· + 1) ++ List.drop (a + 1) l := rfl
  refine (crk_filter_split (phiPivot a l) hsplit ?_ ?_).trans ?_
  · intro x hx
    rw [hpiv]
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_iff_getElem] at hu
    obtain ⟨i, hi, hui⟩ := hu
    rw [List.getElem_take] at hui
    have hi_len : i < l.length := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hia : i < a := by
      have hii := hi
      rw [List.length_take] at hii
      omega
    have hle := (List.pairwise_iff_getElem.mp hl) i a hi_len hlen hia
    omega
  · intro y hy
    rw [hpiv]
    rw [List.mem_iff_getElem] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    rw [List.getElem_drop] at hyj
    have hj_len : (a + 1) + j < l.length := by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega
    have hle := (List.pairwise_iff_getElem.mp hl) a ((a + 1) + j) hlen hj_len
      (by omega)
    omega
  · rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hlen)]

theorem crk_phi_pivot_big (k a : ℕ) (l : List ℕ)
    (hlen : a < l.length) (hbig : a + k < l[a]) :
    a + k + 1 ≤ phiPivot a l := by
  unfold phiPivot
  rw [List.getD_eq_getElem _ _ hlen]
  exact hbig

/-! ## Backward list map -/

theorem crk_psi_sorted (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    (psiList c m).Pairwise (· ≥ ·) := by
  have hspec := crk_sorted_filter_spec m hm c
  have htake : ∀ x ∈ List.take (psiCount c m) m, c < x := hspec.2.1
  have hdrop : ∀ x ∈ List.drop (psiCount c m) m, x ≤ c := hspec.2.2
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hpre : ((List.take (psiCount c m) m).map (· - 1)).Pairwise (· ≥ ·) := by
    rw [List.pairwise_map]
    exact (hm.sublist (List.take_sublist _ _)).imp (fun h => by omega)
  have hsuf : (c :: List.drop (psiCount c m) m).Pairwise (· ≥ ·) := by
    rw [List.pairwise_cons]
    exact ⟨fun y hy => hdrop y hy, hm.sublist (List.drop_sublist _ _)⟩
  have hacross : ∀ x ∈ (List.take (psiCount c m) m).map (· - 1),
      ∀ y ∈ c :: List.drop (psiCount c m) m, x ≥ y := by
    intro x hx y hy
    rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    rw [List.mem_cons] at hy
    rcases hy with rfl | hy
    · have hu2 := htake u hu
      omega
    · have hu2 := htake u hu
      have hy2 := hdrop y hy
      omega
  rw [hpsplit, List.pairwise_append]
  exact ⟨hpre, hsuf, hacross⟩

theorem crk_psi_ge_two (k c : ℕ) (m : List ℕ) (hk : 1 ≤ k)
    (hm : m.Pairwise (· ≥ ·)) (h2 : ∀ x ∈ m, 2 ≤ x)
    (hbig : psiCount c m + k + 1 ≤ c) :
    ∀ x ∈ psiList c m, 2 ≤ x := by
  have hspec := crk_sorted_filter_spec m hm c
  have htake : ∀ x ∈ List.take (psiCount c m) m, c < x := hspec.2.1
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hmem_drop : ∀ y ∈ List.drop (psiCount c m) m, y ∈ m := by
    intro y hy
    rw [List.mem_iff_getElem] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    rw [List.getElem_drop] at hyj
    rw [← hyj]
    exact List.getElem_mem (by
      have hjj := hj
      rw [List.length_drop] at hjj
      omega)
  intro x hx
  rw [hpsplit, List.mem_append, List.mem_cons] at hx
  rcases hx with hx | rfl | hx
  · rw [List.mem_map] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hu2 := htake u hu
    omega
  · omega
  · exact h2 x (hmem_drop x hx)

theorem crk_psi_sum (c : ℕ) (m : List ℕ)
    (h2 : ∀ x ∈ m, 2 ≤ x) :
    psiCount c m + (psiList c m).sum = c + m.sum := by
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hbdef : psiCount c m = (m.filter (fun x => decide (c < x))).length := rfl
  have hble : psiCount c m ≤ m.length := by
    rw [hbdef]
    exact List.length_filter_le _ _
  have hmem_take : ∀ u ∈ List.take (psiCount c m) m, u ∈ m := by
    intro u hu
    rw [List.mem_iff_getElem] at hu
    obtain ⟨i, hi, hui⟩ := hu
    rw [List.getElem_take] at hui
    rw [← hui]
    exact List.getElem_mem (by
      have hii := hi
      rw [List.length_take] at hii
      omega)
  have htsum : (List.take (psiCount c m) m).sum + (List.drop (psiCount c m) m).sum
      = m.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hmap : ((List.take (psiCount c m) m).map (· - 1)).sum + psiCount c m
      = (List.take (psiCount c m) m).sum := by
    have hround : ((List.take (psiCount c m) m).map (· - 1)).map (· + 1)
        = List.take (psiCount c m) m := by
      rw [List.map_map]
      have hcongr : (List.take (psiCount c m) m).map ((· + 1) ∘ (· - 1))
          = (List.take (psiCount c m) m).map id :=
        List.map_congr_left (fun u hu => by
          have hu2 : 2 ≤ u := h2 u (hmem_take u hu)
          have h1 : 1 ≤ u := by omega
          exact Nat.sub_add_cancel h1)
      rw [hcongr, List.map_id]
    have hsum := congrArg List.sum hround
    rw [crk_sum_map_succ, List.length_map] at hsum
    have htake_len : (List.take (psiCount c m) m).length = psiCount c m := by
      rw [List.length_take, Nat.min_eq_left hble]
    rw [htake_len] at hsum
    exact hsum
  rw [hpsplit, List.sum_append, List.sum_cons]
  omega

theorem crk_psi_length (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    psiCount c m < (psiList c m).length := by
  have hspec := crk_sorted_filter_spec m hm c
  have hbdef : psiCount c m = (m.filter (fun x => decide (c < x))).length := rfl
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  rw [hpsplit, List.length_append, List.length_map, List.length_cons, hbdef]
  have htake_len : (List.take (m.filter (fun x => decide (c < x))).length m).length
      = (m.filter (fun x => decide (c < x))).length := by
    rw [List.length_take, Nat.min_eq_left hspec.1]
  rw [htake_len]
  omega

theorem crk_psi_pivot (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    (psiList c m).getD (psiCount c m) 0 = c := by
  have hspec := crk_sorted_filter_spec m hm c
  have hbdef : psiCount c m = (m.filter (fun x => decide (c < x))).length := rfl
  have hble : psiCount c m ≤ m.length := by
    rw [hbdef]
    exact hspec.1
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have htake_len : (List.take (psiCount c m) m).length = psiCount c m := by
    rw [List.length_take, Nat.min_eq_left hble]
  have hmap_len : ((List.take (psiCount c m) m).map (· - 1)).length
      = psiCount c m := by
    rw [List.length_map]
    exact htake_len
  have hlen : psiCount c m < (psiList c m).length :=
    crk_psi_length c m hm
  have hget : (psiList c m).getD (psiCount c m) 0
      = (psiList c m)[psiCount c m]'hlen := List.getD_eq_getElem _ _ hlen
  rw [hget]
  simp only [hpsplit, List.getElem_append_right (le_of_eq hmap_len), hmap_len,
    Nat.sub_self, List.getElem_cons_zero]

/-! ## List maps are inverse -/

theorem crk_psi_phi (a : ℕ) (l : List ℕ)
    (hl : l.Pairwise (· ≥ ·)) (hlen : a < l.length) :
    psiCount (phiPivot a l) (phiList a l) = a ∧
    psiList (phiPivot a l) (phiList a l) = l := by
  have hpiv : phiPivot a l = l[a]'hlen := List.getD_eq_getElem _ _ hlen
  have hcount1 : psiCount (phiPivot a l) (phiList a l) = a :=
    crk_phi_filter a l hl hlen
  refine ⟨hcount1, ?_⟩
  have hsplit_phi : phiList a l =
      (List.take a l).map (· + 1) ++ List.drop (a + 1) l := rfl
  have hmaplen : ((List.take a l).map (· + 1)).length = a := by
    rw [List.length_map, List.length_take, Nat.min_eq_left (le_of_lt hlen)]
  have htake : List.take a (phiList a l) = (List.take a l).map (· + 1) := by
    rw [hsplit_phi]
    exact List.take_left' hmaplen
  have hdrop : List.drop a (phiList a l) = List.drop (a + 1) l := by
    rw [hsplit_phi]
    exact List.drop_left' hmaplen
  have hmapback : ((List.take a l).map (· + 1)).map (· - 1) = List.take a l := by
    rw [List.map_map]
    exact List.map_id'' (fun x => Nat.add_sub_cancel x 1) _
  have hda : List.drop a l = l[a]'hlen :: List.drop (a + 1) l :=
    List.drop_eq_getElem_cons hlen
  have hpsplit : psiList (phiPivot a l) (phiList a l) =
      (List.take (psiCount (phiPivot a l) (phiList a l)) (phiList a l)).map (· - 1) ++
      phiPivot a l ::
        List.drop (psiCount (phiPivot a l) (phiList a l)) (phiList a l) := rfl
  rw [hpsplit, hcount1, hpiv, htake, hdrop, hmapback, ← hda, List.take_append_drop]

theorem crk_phi_psi (c : ℕ) (m : List ℕ)
    (hm : m.Pairwise (· ≥ ·)) :
    (psiList c m).getD (psiCount c m) 0 = c ∧
    phiList (psiCount c m) (psiList c m) = m := by
  have hspec := crk_sorted_filter_spec m hm c
  have htake : ∀ x ∈ List.take (psiCount c m) m, c < x := hspec.2.1
  have hble : psiCount c m ≤ m.length := hspec.1
  have hpsplit : psiList c m =
      (List.take (psiCount c m) m).map (· - 1) ++ c :: List.drop (psiCount c m) m := rfl
  have hmaplen : ((List.take (psiCount c m) m).map (· - 1)).length
      = psiCount c m := by
    rw [List.length_map, List.length_take, Nat.min_eq_left hble]
  have hget : (psiList c m).getD (psiCount c m) 0 = c :=
    crk_psi_pivot c m hm
  refine ⟨hget, ?_⟩
  have htake2 : List.take (psiCount c m) (psiList c m)
      = (List.take (psiCount c m) m).map (· - 1) := by
    rw [hpsplit]
    exact List.take_left' hmaplen
  have hdrop2 : List.drop (psiCount c m + 1) (psiList c m)
      = List.drop (psiCount c m) m := by
    rw [hpsplit]
    have heq : psiCount c m + 1
        = ((List.take (psiCount c m) m).map (· - 1)).length + 1 := by
      rw [hmaplen]
    rw [heq, List.drop_length_add_append]
    exact rfl
  have hround : ((List.take (psiCount c m) m).map (· - 1)).map (· + 1)
      = List.take (psiCount c m) m := by
    rw [List.map_map]
    have hcongr : (List.take (psiCount c m) m).map ((· + 1) ∘ (· - 1))
        = (List.take (psiCount c m) m).map id :=
      List.map_congr_left (fun u hu => by
        have huc := htake u hu
        have h1 : 1 ≤ u := by omega
        exact Nat.sub_add_cancel h1)
    rw [hcongr, List.map_id]
  have hphsplit : phiList (psiCount c m) (psiList c m) =
      (List.take (psiCount c m) (psiList c m)).map (· + 1) ++
      List.drop (psiCount c m + 1) (psiList c m) := rfl
  rw [hphsplit, htake2, hdrop2, hround, List.take_append_drop]

/-! ## Lifting to partitions -/

theorem crk_phi_index (k L : ℕ) (hk : 1 ≤ k) (π : Nat.Partition L)
    (hπ : highPartsCond k π) :
    Multiset.count 1 π.parts < (nonOneParts π).length ∧
    Multiset.count 1 π.parts + k
      < phiPivot (Multiset.count 1 π.parts) (nonOneParts π) := by
  have hle1 : Multiset.count 1 π.parts + 1 ≤
      ((nonOneParts π).filter
        (fun x => decide (Multiset.count 1 π.parts + k < x))).length := by
    have hπ' := hπ
    unfold highPartsCond at hπ'
    rwa [crk_filter_threshold π (Multiset.count 1 π.parts + k) (by omega)] at hπ'
  have hlen : Multiset.count 1 π.parts < (nonOneParts π).length := by
    have hb := (crk_sorted_filter_spec (nonOneParts π) (crk_nonOne_sorted π)
      (Multiset.count 1 π.parts + k)).1
    omega
  refine ⟨hlen, ?_⟩
  have hpiv : phiPivot (Multiset.count 1 π.parts) (nonOneParts π)
      = (nonOneParts π)[Multiset.count 1 π.parts]'hlen :=
    List.getD_eq_getElem _ _ hlen
  rw [hpiv]
  have hiff := crk_mem_filter_iff (nonOneParts π) (crk_nonOne_sorted π)
    (Multiset.count 1 π.parts + k) (Multiset.count 1 π.parts) hlen
  exact hiff.mp hle1

end CrankNonneg
end MetaMathlibExt
