/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.WellFounded
import Mathlib.Order.Lattice.Nat
import Def.GameTheory.SpragueGrundy.Part3


namespace MetaMathlibExt.SpragueGrundy

theorem exists_move_with_grundy (G : ImpartialGame) (p : G.Pos) {m : ℕ}
    (h : m < grundy G p) :
    ∃ q ∈ G.moves p, grundy G q = m := by
  have hmem : m ∈ ((G.moves p).attach.image
      (fun x : { q // q ∈ G.moves p } => grundy G x.val)) :=
    mem_of_lt_mex _ (grundy_eq G p ▸ h)
  rw [Finset.mem_image] at hmem
  obtain ⟨x, _, hxeq⟩ := hmem
  exact ⟨x.val, x.property, hxeq⟩

theorem grundy_ne_of_mem (G : ImpartialGame) {p q : G.Pos}
    (h : q ∈ G.moves p) : grundy G q ≠ grundy G p := by
  intro heq
  have hmem : grundy G p ∈ ((G.moves p).attach.image
      (fun x : { qq // qq ∈ G.moves p } => grundy G x.val)) := by
    rw [← heq]
    exact Finset.mem_image.mpr ⟨⟨q, h⟩, Finset.mem_attach _ _, rfl⟩
  exact mex_not_mem _ (grundy_eq G p ▸ hmem)

theorem nim_grundy_aux (n : ℕ) (v : ℕ) (k : Fin (n + 1)) (hk : k.val ≤ v) :
    grundy (nimHeap n) k = k.val := by
  induction v generalizing k with
  | zero =>
    have hk0 : k.val = 0 := by omega
    have him : ((nimHeap n).moves k).attach.image
        (fun x : { q // q ∈ (nimHeap n).moves k } => grundy (nimHeap n) x.val) =
        Finset.range k.val := by
      ext w
      simp only [Finset.mem_image, Finset.mem_attach, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        have hmemFin : (x.val : Fin (n + 1)) ∈
            Finset.univ.filter (fun j : Fin (n + 1) => j.val < k.val) :=
          x.property
        have hmem := (Finset.mem_filter.mp hmemFin).2
        rw [hk0] at hmem
        exact absurd hmem (Nat.not_lt_zero _)
      · intro hw
        rw [hk0] at hw
        exact absurd hw (Nat.not_lt_zero _)
    have hge := grundy_eq (nimHeap n) k
    rw [hge, him, mex_range]
  | succ v ih =>
    have him : ((nimHeap n).moves k).attach.image
        (fun x : { q // q ∈ (nimHeap n).moves k } => grundy (nimHeap n) x.val) =
        Finset.range k.val := by
      ext w
      simp only [Finset.mem_image, Finset.mem_attach, true_and,
        Finset.mem_range]
      constructor
      · rintro ⟨x, hx⟩
        have hmemFin : (x.val : Fin (n + 1)) ∈
            Finset.univ.filter (fun j : Fin (n + 1) => j.val < k.val) :=
          x.property
        have hmem := (Finset.mem_filter.mp hmemFin).2
        have hlt : (x.val : Fin (n + 1)).val < v + 1 :=
          Nat.lt_of_lt_of_le hmem hk
        have hle : (x.val : Fin (n + 1)).val ≤ v :=
          Nat.le_of_lt_succ hlt
        have hgx : grundy (nimHeap n) (x.val : Fin (n + 1)) = (x.val : Fin (n + 1)).val :=
          ih (x.val : Fin (n + 1)) hle
        have hxw : (x.val : Fin (n + 1)).val = w := hgx.symm.trans hx
        rw [← hxw]
        exact hmem
      · intro hw
        have hkle : k.val ≤ n := Nat.le_of_lt_succ k.isLt
        have hlt : w < n + 1 := Nat.lt_of_lt_of_le hw (Nat.le_succ_of_le hkle)
        let j : Fin (n + 1) := ⟨w, hlt⟩
        have hmemFin : j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val < k.val) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
        have hjmem : j ∈ (nimHeap n).moves k := hmemFin
        refine ⟨⟨j, hjmem⟩, ?_⟩
        have hle : (j : Fin (n + 1)).val ≤ v := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hw hk)
        have hgj : grundy (nimHeap n) j = (j : Fin (n + 1)).val := ih j hle
        have hjw : (j : Fin (n + 1)).val = w := rfl
        rw [hjw] at hgj
        exact hgj
    have hge := grundy_eq (nimHeap n) k
    rw [hge, him, mex_range]

theorem nim_grundy (n : ℕ) (k : Fin (n + 1)) :
    grundy (nimHeap n) k = k.val :=
  nim_grundy_aux n k.val k (Nat.le_refl _)

theorem isP_sum_iff_aux (G H : ImpartialGame) (t : ℕ) (a : G.Pos) (b : H.Pos)
    (hle : G.rank a + H.rank b ≤ t) :
    IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
      (grundy G a ^^^ grundy H b = 0) := by
  induction t generalizing a b with
  | zero =>
    have ha0 : G.rank a = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_add_right _ _) hle)
    have hb0 : H.rank b = 0 :=
      Nat.le_zero.mp (Nat.le_trans (Nat.le_add_left _ _) hle)
    have hemptyA : G.moves a = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hlt := G.rank_lt a x hx
      rw [ha0] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
    have hemptyB : H.moves b = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hlt := H.rank_lt b x hx
      rw [hb0] at hlt
      exact absurd hlt (Nat.not_lt_zero _)
    have hsum_empty : (gameSum G H).moves ((a, b) : (gameSum G H).Pos) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro q hq
      have hc := sum_cases G H a b q hq
      cases hc with
      | inl hl =>
        obtain ⟨a', ha', -⟩ := hl
        rw [hemptyA] at ha'
        exact Finset.notMem_empty _ ha'
      | inr hr =>
        obtain ⟨b', hb', -⟩ := hr
        rw [hemptyB] at hb'
        exact Finset.notMem_empty _ hb'
    have hga : grundy G a = 0 := by
      have hge := grundy_eq G a
      rw [hemptyA] at hge
      have him : ((∅ : Finset G.Pos).attach.image
          (fun x : { q // q ∈ (∅ : Finset G.Pos) } => grundy G x.val)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨x, _, -⟩ := Finset.mem_image.mp hy
        exact Finset.notMem_empty _ x.property
      rw [him, mex_empty] at hge
      exact hge
    have hgb : grundy H b = 0 := by
      have hge := grundy_eq H b
      rw [hemptyB] at hge
      have him : ((∅ : Finset H.Pos).attach.image
          (fun x : { q // q ∈ (∅ : Finset H.Pos) } => grundy H x.val)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        obtain ⟨x, _, -⟩ := Finset.mem_image.mp hy
        exact Finset.notMem_empty _ x.property
      rw [him, mex_empty] at hge
      exact hge
    have hl : IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) := by
      rw [IsP_sum_unfold, hsum_empty]
      intro q hq
      exact absurd hq (Finset.notMem_empty q)
    have hr : grundy G a ^^^ grundy H b = 0 := by
      rw [hga, hgb, Nat.xor_self]
    exact iff_of_true hl hr
  | succ t ih =>
    rw [IsP_sum_unfold]
    constructor
    · intro hall
      by_contra hne
      have hxy : grundy G a ≠ grundy H b := by
        intro heq
        apply hne
        rw [heq, Nat.xor_self]
      have htri := lt_trichotomy (grundy G a) (grundy H b)
      cases htri with
      | inl hlt =>
        obtain ⟨b', hb', hgb⟩ := exists_move_with_grundy H b hlt
        have hq := sum_mem_right G H a b b' hb'
        have hlt2 : G.rank a + H.rank b' < G.rank a + H.rank b :=
          Nat.add_lt_add_left (H.rank_lt b b' hb') _
        have hle' : G.rank a + H.rank b' ≤ t :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
        have hi := ih a b' hle'
        have hxor0 : grundy G a ^^^ grundy H b' = 0 := by
          rw [hgb, Nat.xor_self]
        have hP : IsP (gameSum G H) ((a, b') : (gameSum G H).Pos) := hi.mpr hxor0
        exact hall _ hq hP
      | inr hrest =>
        cases hrest with
        | inl heq => exact hxy heq
        | inr hgt =>
          obtain ⟨a', ha', hga⟩ := exists_move_with_grundy G a hgt
          have hq := sum_mem_left G H a b a' ha'
          have hlt2 : G.rank a' + H.rank b < G.rank a + H.rank b :=
            Nat.add_lt_add_right (G.rank_lt a a' ha') _
          have hle' : G.rank a' + H.rank b ≤ t :=
            Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
          have hi := ih a' b hle'
          have hxor0 : grundy G a' ^^^ grundy H b = 0 := by
            rw [hga, Nat.xor_self]
          have hP : IsP (gameSum G H) ((a', b) : (gameSum G H).Pos) := hi.mpr hxor0
          exact hall _ hq hP
    · intro hxor q hq hP
      have hc := sum_cases G H a b q hq
      cases hc with
      | inl hl =>
        obtain ⟨a', ha', heq⟩ := hl
        have hlt2 : G.rank a' + H.rank b < G.rank a + H.rank b :=
          Nat.add_lt_add_right (G.rank_lt a a' ha') _
        have hle2 : G.rank a' + H.rank b ≤ t :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
        have hi := ih a' b hle2
        rw [heq] at hP
        have ha0 : grundy G a' ^^^ grundy H b = 0 := hi.mp hP
        have hea : grundy G a' = grundy H b := xor_eq_zero_iff.mp ha0
        have hxx : grundy G a = grundy H b := xor_eq_zero_iff.mp hxor
        have hne : grundy G a' ≠ grundy G a := grundy_ne_of_mem G ha'
        exact hne (hea.trans hxx.symm)
      | inr hr =>
        obtain ⟨b', hb', heq⟩ := hr
        have hlt2 : G.rank a + H.rank b' < G.rank a + H.rank b :=
          Nat.add_lt_add_left (H.rank_lt b b' hb') _
        have hle2 : G.rank a + H.rank b' ≤ t :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt2 hle)
        have hi := ih a b' hle2
        rw [heq] at hP
        have hb0 : grundy G a ^^^ grundy H b' = 0 := hi.mp hP
        have heb : grundy G a = grundy H b' := xor_eq_zero_iff.mp hb0
        have hxx : grundy G a = grundy H b := xor_eq_zero_iff.mp hxor
        have hne : grundy H b' ≠ grundy H b := grundy_ne_of_mem H hb'
        exact hne (heb.symm.trans hxx)

theorem isP_sum_iff (G H : ImpartialGame) (a : G.Pos) (b : H.Pos) :
    IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
      (grundy G a ^^^ grundy H b = 0) :=
  isP_sum_iff_aux G H _ a b (Nat.le_refl _)

/-- Sprague–Grundy theorem: every finite impartial game is equivalent to a
single Nim heap.

Source: Tanya Khovanova and Joshua Xiong, "Nim Fractals", Journal of Integer
Sequences 17 (2014), lines 101–105,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Khovanova/khova6.tex ;
complete SHA-256 `6f8be9d461ff98b5a7c878830eb169e69ba8dd7540948d9149527fdb5ca7783a`;
normalized span SHA-256 `2228effe253846e7f994ee9ae1695b5a830e5686148e5d9287d1b04eae55fec6`.
Its cited original references: Grundy, Eureka 2 (1939), 6–8, reprinted 27 (1964),
9–11; Sprague, Tôhoku Math. Journal 41 (1935–1936), 438–444.

Proves `Wanted` entry `sprague_grundy`.
-/
theorem sprague_grundy (G : ImpartialGame) :
    ∃ n : ℕ, Equiv G (nimHeap n) := by
  refine ⟨grundy G G.start, fun K => ?_⟩
  have hG := isP_sum_iff G K G.start K.start
  have hN := isP_sum_iff (nimHeap (grundy G G.start)) K
    ((nimHeap (grundy G G.start)).start) K.start
  have hnim : grundy (nimHeap (grundy G G.start))
      ((nimHeap (grundy G G.start)).start) = grundy G G.start := by
    have h := nim_grundy (grundy G G.start) ((nimHeap (grundy G G.start)).start)
    exact h
  rw [hnim] at hN
  exact hG.trans hN.symm

end MetaMathlibExt.SpragueGrundy
