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
import Def.Combinatorics.SimpleGraph.KneserLovasz.Part9
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

theorem knSmall_card_le {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (hcons : knConsistent x)
    (hfp : knFp C x = 0) (hfm : knFm C x = 0) :
    x.card ≤ 2 * k - 2 := by
  have hp := knPos_card_lt_of_fp_zero C hfp
  have hq := knNegIdx_card_lt_of_fm_zero C hfm
  have hc := knConsistent_card_eq hcons
  omega

theorem knLarge_or_small {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N)) (hk : 0 < k)
    {x : Finset (Bool × Fin n)} (hcons : knConsistent x) :
    (knFp C x = 0 ∧ knFm C x = 0) ∨
      knFm C x < knFp C x ∨ knFp C x < knFm C x := by
  by_cases heq : knFp C x = knFm C x
  · left
    have h0 := knFpFm C hk hcons heq
    exact ⟨h0, by omega⟩
  · right
    exact lt_or_gt_of_ne (Ne.symm heq)

theorem knLab_noCompl_empty {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    {y : Finset (Bool × Fin n)} (hconsY : knConsistent y)
    (heq : knLab C hn hk h2 y =
      knNegLabel (knLab C hn hk h2 ∅)) : False := by
  classical
  by_cases hy0 : y = ∅
  · subst hy0
    have hxL := knLab_empty C hn hk h2
    rw [hxL] at heq
    have hfst : (true : Bool) = !true := congrArg Prod.fst heq
    exact (by decide : ¬ ((true : Bool) = !true)) hfst
  · have hyNonempty : y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hy0
    have hval : ((knLab C hn hk h2 y).2).val = n - 1 := by
      have h := congrArg Fin.val (congrArg Prod.snd heq)
      rw [knLab_empty C hn hk h2] at h
      exact h
    rcases knLarge_or_small C hk hconsY with ⟨hfp0, hfm0⟩ | hpos | hneg
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          min (y.card - 1) (n - 1) := by
        have hLy := knLab_small C hn hk h2 hy0 hfp0 hfm0
        simp only [hLy, knLabSmall_snd_val]
      have hne2 := knSmall_val_ne hk h2 hyNonempty
        (knSmall_card_le C hconsY hfp0 hfm0)
      omega
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          (knFp C y - 1) + 2 * (k - 1) := by
        have hlarge : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlarge hpos (by omega)
        simp only [hLy, knLabLargePos_snd_val]
      have hne2 := knLarge_val_ne hk h2 (knFp C y) (by omega) (knFp_le C y)
      omega
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          (knFm C y - 1) + 2 * (k - 1) := by
        have hlarge : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlarge (by omega)
          (by omega)
        simp only [hLy, knLabLargeNeg_snd_val]
      have hne2 := knLarge_val_ne hk h2 (knFm C y) (by omega) (knFm_le C y)
      omega

theorem knLab_noCompl {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knNoCompl (knLab C hn hk h2) := by
  classical
  intro x y hconsX hconsY hsub heq
  by_cases hx0 : x = ∅
  · subst hx0
    exact knLab_noCompl_empty C hn hk h2 hconsY heq
  · have hxNonempty : x.Nonempty := Finset.nonempty_iff_ne_empty.mpr hx0
    have hyne : y.Nonempty := by
      obtain ⟨l, hl⟩ := hxNonempty
      exact ⟨l, hsub hl⟩
    have hy0 : y ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hyne
    rcases knLarge_or_small C hk hconsX with ⟨hfp0, hfm0⟩ | hposX | hnegX
    · have hval := congrArg Fin.val (congrArg Prod.snd heq)
      rw [knNegLabel_snd] at hval
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hLy := knLab_small C hn hk h2 hy0 hfp0y hfm0y
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            min (y.card - 1) (n - 1) := by
          simp only [hLy, knLabSmall_snd_val]
        have hle_x := knSmall_card_le C hconsX hfp0 hfm0
        have hle_y := knSmall_card_le C hconsY hfp0y hfm0y
        have hx1 : 1 ≤ x.card := Finset.one_le_card.mpr hxNonempty
        have hy1 : 1 ≤ y.card := Finset.one_le_card.mpr hyne
        have hcardxy : x.card = y.card := by omega
        have hxy : x = y :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 y).1) := by
          have h := congrArg Prod.fst heq
          rw [hxy] at h
          exact h
        cases hbx : (knLab C hn hk h2 y).1 with
        | true =>
          rw [hbx] at hfst
          exact (by decide : ¬ ((true : Bool) = !true)) hfst
        | false =>
          rw [hbx] at hfst
          exact (by decide : ¬ ((false : Bool) = !false)) hfst
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFp C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargePos_snd_val]
        have hlt := knSmall_val_lt hk hxNonempty
          (knSmall_card_le C hconsX hfp0 hfm0)
        have hge : 2 * (k - 1) ≤ (knFp C y - 1) + 2 * (k - 1) := by
          omega
        omega
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFm C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargeNeg_snd_val]
        have hlt := knSmall_val_lt hk hxNonempty
          (knSmall_card_le C hconsX hfp0 hfm0)
        have hge : 2 * (k - 1) ≤ (knFm C y - 1) + 2 * (k - 1) := by
          omega
        omega
    · have hlargeX : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by
        intro hcon; omega
      have hLx := knLab_large_pos C hn hk h2 hx0 hlargeX hposX
        (by omega)
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        omega
      · have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 x).1) :=
          congrArg Prod.fst heq
        rw [hLy, hLx, knLabLargePos_fst, knLabLargePos_fst] at hfst
        exact (by decide : ¬ ((true : Bool) = !true)) hfst
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hval := congrArg Fin.val (congrArg Prod.snd heq)
        rw [knNegLabel_snd] at hval
        have hLxv : ((knLab C hn hk h2 x).2).val =
            (knFp C x - 1) + 2 * (k - 1) := by
          simp only [hLx, knLabLargePos_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFm C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargeNeg_snd_val]
        omega
    · have hlargeX : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by
        intro hcon; omega
      have hLx := knLab_large_neg C hn hk h2 hx0 hlargeX (by omega)
        (by omega)
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        omega
      · have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hval := congrArg Fin.val (congrArg Prod.snd heq)
        rw [knNegLabel_snd] at hval
        have hLxv : ((knLab C hn hk h2 x).2).val =
            (knFm C x - 1) + 2 * (k - 1) := by
          simp only [hLx, knLabLargeNeg_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFp C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargePos_snd_val]
        omega
      · have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 x).1) :=
          congrArg Prod.fst heq
        rw [hLy, hLx, knLabLargeNeg_fst, knLabLargeNeg_fst] at hfst
        exact (by decide : ¬ ((false : Bool) = !false)) hfst

theorem knLab_antipodal {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knAntipodal (knLab C hn hk h2) := by
  classical
  intro x hcons hxne
  have hne : x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hxne
  have hcard : 0 < x.card := Finset.card_pos.mpr hxne
  have hneN : (knNegCell x).Nonempty := by
    apply Finset.card_pos.mp
    rw [knNegCell_card]
    exact hcard
  have hneN' : knNegCell x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hneN
  have hfpN : knFp C (knNegCell x) = knFm C x := knFp_negCell C x
  have hfmN : knFm C (knNegCell x) = knFp C x := knFm_negCell C x
  rcases knLarge_or_small C hk hcons with ⟨hfp0, hfm0⟩ | hpos | hneg
  · have hfpN0 : knFp C (knNegCell x) = 0 := by rw [hfpN]; exact hfm0
    have hfmN0 : knFm C (knNegCell x) = 0 := by rw [hfmN]; exact hfp0
    have hLx := knLab_small C hn hk h2 hne hfp0 hfm0
    have hLN := knLab_small C hn hk h2 hneN' hfpN0 hfmN0
    rw [hLx, hLN]
    apply Prod.ext
    · simp only [knLabSmall_fst, knNegLabel_fst, knLabSmall_fst,
        knMinIdx_negCell hxne hneN, knTrue_mem_negCell]
      rcases knConsistent_bool_exact hcons
        (knMinIdx_mem hxne) with ⟨ht, hf⟩ | ⟨hf, ht⟩
      · rw [decide_eq_false hf, decide_eq_true ht]
        rfl
      · rw [decide_eq_true hf, decide_eq_false ht]
        rfl
    · apply Fin.ext
      rw [knLabSmall_snd_val, knNegLabel_snd, knLabSmall_snd_val,
        knNegCell_card]
  · have hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by intro hcon; omega
    have hfp1 : 1 ≤ knFp C x := by omega
    have hLx := knLab_large_pos C hn hk h2 hne hlarge hpos hfp1
    have hlargeN : ¬ (knFp C (knNegCell x) = 0 ∧
        knFm C (knNegCell x) = 0) := by
      rw [hfpN, hfmN]; intro hcon; omega
    have hnegN : ¬ knFm C (knNegCell x) < knFp C (knNegCell x) := by
      rw [hfpN, hfmN]; omega
    have hfmN1 : 1 ≤ knFm C (knNegCell x) := by rw [hfmN]; omega
    have hLN := knLab_large_neg C hn hk h2 hneN' hlargeN hnegN hfmN1
    rw [hLx, hLN]
    unfold knLabLargeNeg knLabLargePos knNegLabel
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [Fin.mk.injEq, hfmN]
  · have hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by intro hcon; omega
    have hfm1 : 1 ≤ knFm C x := by omega
    have hLx := knLab_large_neg C hn hk h2 hne hlarge (by omega) hfm1
    have hlargeN : ¬ (knFp C (knNegCell x) = 0 ∧
        knFm C (knNegCell x) = 0) := by
      rw [hfpN, hfmN]; intro hcon; omega
    have hposN : knFm C (knNegCell x) < knFp C (knNegCell x) := by
      rw [hfpN, hfmN]; omega
    have hfpN1 : 1 ≤ knFp C (knNegCell x) := by rw [hfpN]; omega
    have hLN := knLab_large_pos C hn hk h2 hneN' hlargeN hposN hfpN1
    rw [hLx, hLN]
    unfold knLabLargeNeg knLabLargePos knNegLabel
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [Fin.mk.injEq, hfpN]

theorem knNotColorable {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n) :
    ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) := by
  intro hC
  obtain ⟨C⟩ := hC
  have hn : 0 < n := by omega
  obtain ⟨x, y, hconsX, hconsY, hsub, heq⟩ :=
    knTucker (knLab C hn hk h2) (knLab_antipodal C hn hk h2)
  exact knLab_noCompl C hn hk h2 x y hconsX hconsY hsub heq

/--
For 0<k and 2k≤n the Kneser graph on k-subsets has chromatic number n-2k+2.
Source: L. Lovasz, JCT A 25 (1978), 319-324, DOI 10.1016/0097-3165(78)90022-5.

Proves `Wanted` entry `kneser_lovasz`.
-/
theorem kneser_lovasz {n k : ℕ} (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ∞) := by
  have hcast : (n - 2 * k + 2 : ℕ∞) =
      (((n - 2 * k + 1 : ℕ) : ℕ∞) + 1) := by
    have e1 : ((2 * k : ℕ) : ℕ∞) = 2 * (↑k : ℕ∞) := by push_cast; ring
    have e2 : ((n - 2 * k : ℕ) : ℕ∞) =
        (↑n : ℕ∞) - ((2 * k : ℕ) : ℕ∞) :=
      ENat.natCast_sub n (2 * k)
    have e4 : ((n - 2 * k + 1 : ℕ) : ℕ∞) =
        ((n - 2 * k : ℕ) : ℕ∞) + 1 := by
      push_cast
      ring
    rw [← e1, ← e2, e4]
    ring
  rw [hcast, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  refine ⟨knUpperColoring hk h, knNotColorable hk h⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
