/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Def.Combinatorics.SimpleGraph.KneserLovasz.Part8
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

theorem knFpFm {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (hk : 0 < k) {x : Finset (Bool × Fin n)} (hcons : knConsistent x)
    (heq : knFp C x = knFm C x) : knFp C x = 0 := by
  classical
  by_contra hpos
  have hpos' : 0 < knFp C x := Nat.pos_of_ne_zero hpos
  have hneP : ((knPos x).powersetCard k).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsup0 : knFp C x ≤ 0 := by
      unfold knFp
      rw [Finset.sup_le_iff]
      intro B hB
      rw [hempty] at hB
      exact absurd hB (Finset.notMem_empty B)
    omega
  obtain ⟨A, hAmem, hAmax⟩ :=
    Finset.exists_max_image _ (knCp C) hneP
  have hAsup : knFp C x = knCp C A := by
    apply le_antisymm
    · unfold knFp
      rw [Finset.sup_le_iff]
      exact hAmax
    · unfold knFp
      exact Finset.le_sup hAmem
  have hAsub : A ⊆ knPos x := (Finset.mem_powersetCard.mp hAmem).1
  have hAcard : A.card = k := by
    by_contra hne2
    have hzero : knCp C A = 0 := knCp_ne C hne2
    omega
  have hAval : (C ⟨A, hAcard⟩).val + 1 = knFp C x := by
    have hcp := knCp_eq C hAcard
    omega
  have hneM : ((knNegIdx x).powersetCard k).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsup0 : knFm C x ≤ 0 := by
      unfold knFm
      rw [Finset.sup_le_iff]
      intro B hB
      rw [hempty] at hB
      exact absurd hB (Finset.notMem_empty B)
    omega
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image _ (knCp C) hneM
  have hBsup : knFm C x = knCp C B := by
    apply le_antisymm
    · unfold knFm
      rw [Finset.sup_le_iff]
      exact hBmax
    · unfold knFm
      exact Finset.le_sup hBmem
  have hBsub : B ⊆ knNegIdx x := (Finset.mem_powersetCard.mp hBmem).1
  have hBcard : B.card = k := by
    by_contra hne2
    have hzero : knCp C B = 0 := knCp_ne C hne2
    omega
  have hBval : (C ⟨B, hBcard⟩).val + 1 = knFm C x := by
    have hcp := knCp_eq C hBcard
    omega
  have hposmem : ∀ a ∈ A, (true, a) ∈ x := by
    intro a ha
    have haP : a ∈ knPos x := hAsub ha
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp haP
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    have hle : l = (true, a) := Prod.ext hl1 hll
    rw [hle] at hl
    exact Finset.mem_of_mem_filter _ hl
  have hnegmem : ∀ a ∈ B, (false, a) ∈ x := by
    intro a ha
    have haP : a ∈ knNegIdx x := hBsub ha
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp haP
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    have hle : l = (false, a) := Prod.ext hl1 hll
    rw [hle] at hl
    exact Finset.mem_of_mem_filter _ hl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ht := hposmem a ha
    have hf := hnegmem a hb
    exact hcons _ ht hf
  have hneAB : A ≠ B := by
    intro heqAB
    have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hAcard]; exact hk)
    obtain ⟨a, ha⟩ := hAne
    have haB : a ∈ B := heqAB ▸ ha
    exact (Finset.disjoint_left.mp hdisj ha) haB
  have hadjG : (kneserGraph n k).Adj ⟨A, hAcard⟩ ⟨B, hBcard⟩ :=
    ⟨hdisj, fun he => hneAB (congrArg Subtype.val he)⟩
  have hCne := C.valid hadjG
  have hCeq : C ⟨A, hAcard⟩ = C ⟨B, hBcard⟩ := by
    apply Fin.ext
    omega
  exact hCne hCeq

theorem knFp_le {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : knFp C x ≤ N := by
  unfold knFp
  rw [Finset.sup_le_iff]
  intro B _
  by_cases hB : B.card = k
  · rw [knCp_eq C hB]
    have hlt := (C ⟨B, hB⟩).isLt
    omega
  · rw [knCp_ne C hB]
    exact Nat.zero_le N

theorem knFm_le {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : knFm C x ≤ N := by
  unfold knFm
  rw [Finset.sup_le_iff]
  intro B _
  by_cases hB : B.card = k
  · rw [knCp_eq C hB]
    have hlt := (C ⟨B, hB⟩).isLt
    omega
  · rw [knCp_ne C hB]
    exact Nat.zero_le N

theorem knCp_pos_of_card {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card = k) : 0 < knCp C A := by
  rw [knCp_eq C h]
  omega

theorem knPos_card_lt_of_fp_zero {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (h0 : knFp C x = 0) :
    (knPos x).card < k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcon
  have hmem : A ∈ Finset.powersetCard k (knPos x) :=
    Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩
  have hle : knCp C A ≤ knFp C x := Finset.le_sup hmem
  have hpos := knCp_pos_of_card C hAcard
  omega

theorem knNegIdx_card_lt_of_fm_zero {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (h0 : knFm C x = 0) :
    (knNegIdx x).card < k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcon
  have hmem : A ∈ Finset.powersetCard k (knNegIdx x) :=
    Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩
  have hle : knCp C A ≤ knFm C x := Finset.le_sup hmem
  have hpos := knCp_pos_of_card C hAcard
  omega

theorem knLargeIdx_lt {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
    (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
    (f - 1) + 2 * (k - 1) < n := by
  omega

theorem knMinLt {n : ℕ} (a : ℕ) (hn : 0 < n) :
    min a (n - 1) < n := by
  have h := Nat.min_le_right a (n - 1)
  omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
