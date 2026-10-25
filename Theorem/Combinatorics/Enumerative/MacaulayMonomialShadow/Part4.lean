/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple
import Def.Combinatorics.Enumerative.MacaulayMonomialShadow.Part3


namespace MetaMathlibExt

open BigOperators

section

/-- Macaulay multiset-shadow lower bound (Theorem M).

Finitely supported exponent vectors `ℕ →₀ ℕ` model monomials/multisets of a
fixed degree; the union of single-positive-exponent deletions `a.update i (a i - 1)`
over `i ∈ a.support` is the shadow. The explicit `digits i = 0` branch preserves
the empty-family convention, since natural subtraction followed by
`Nat.choose 0 0` would otherwise count a spurious term.

Source: Bernardo M. Ábrego, Silvia Fernández-Merchant, and Bernardo Llano,
"An Inequality for Macaulay Functions," Journal of Integer Sequences 14 (2011),
Theorem M, lines 215–223.
Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Abrego/abrego2.tex>.
Full-source SHA-256
`0a56d8b3c040a0fb5bb57262e0605376eddfdc967da9d2fd58b37f3e4bad64ed`.
Theorem-span SHA-256
`4e9a68f171676aeb3dd5c8c605faa0e677f46e831861a5ccb74de985dd6ffa87`.

Proves `Wanted` entry `macaulay_multiset_shadow_minimal`.

Proof: We formalize the binomial-cascade split inequality and coordinate-slice induction of
Ábrego, Fernández-Merchant, and Llano, their route from Theorem 1 to Theorem M.
-/
theorem macaulay_multiset_shadow_minimal
    (k : ℕ) (A : Finset (ℕ →₀ ℕ)) (digits : Fin (k + 1) → ℕ)
    (hdegree : ∀ a ∈ A, a.sum (fun _ e => e) = k + 1)
    (hstrict : StrictMono digits)
    (hcard : A.card = ∑ i, Nat.choose (digits i) (i.1 + 1)) :
    (∑ i, if digits i = 0 then 0 else Nat.choose (digits i - 1) i.1) ≤
      (A.biUnion fun a => a.support.image fun i => a.update i (a i - 1)).card := by
  induction hm : k + A.card using Nat.strong_induction_on generalizing k A digits with
  | h n ih =>
  obtain rfl | k := k
  · exact macaulay_degree_one A digits hdegree hcard
  · by_cases hA : A.Nonempty
    · obtain ⟨seed, hseed⟩ := hA
      have hseedSupp : seed.support.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        have hseedZero : seed = 0 := Finsupp.support_eq_empty.mp h
        have hdeg := hdegree seed hseed
        rw [hseedZero] at hdeg
        simp at hdeg
      obtain ⟨p, hp⟩ := hseedSupp
      have hseedp : seed p ≠ 0 := Finsupp.mem_support_iff.mp hp
      let P := A.filter fun a => a p ≠ 0
      let C := A.filter fun a => a p = 0
      let B := P.image (mms_lower p)
      have hPsubset : P ⊆ A := by
        intro a ha
        exact (Finset.mem_filter.mp ha).1
      have hCsubset : C ⊆ A := by
        intro a ha
        exact (Finset.mem_filter.mp ha).1
      have hPpos : ∀ a ∈ P, a p ≠ 0 := by
        intro a ha
        exact (Finset.mem_filter.mp ha).2
      have hCzero : ∀ a ∈ C, a p = 0 := by
        intro a ha
        exact (Finset.mem_filter.mp ha).2
      have hseedP : seed ∈ P := Finset.mem_filter.mpr ⟨hseed, hseedp⟩
      have hPnonempty : P.Nonempty := ⟨seed, hseedP⟩
      have hBcard : B.card = P.card := by
        dsimp [B]
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        exact mms_lower_inj p (hPpos a ha) (hPpos b hb) hab
      have hPCcard : P.card + C.card = A.card := by
        have h := Finset.card_filter_add_card_filter_not (s := A) (fun a => a p ≠ 0)
        simpa only [P, C, not_ne_iff] using h
      have hcardSplit : B.card + C.card = A.card := by omega
      have hCcardLt : C.card < A.card := by
        have hPcard : 0 < P.card := Finset.card_pos.mpr hPnonempty
        omega
      have hBcardLe : B.card ≤ A.card := by omega
      have hBsubsetShadow : B ⊆ mms_shadow A := by
        intro b hb
        rw [Finset.mem_image] at hb
        obtain ⟨a, ha, rfl⟩ := hb
        rw [mms_shadow, Finset.mem_biUnion]
        refine ⟨a, hPsubset ha, Finset.mem_image.mpr ⟨p, ?_, rfl⟩⟩
        exact Finsupp.mem_support_iff.mpr (hPpos a ha)
      have hBdegree : ∀ b ∈ B, b.sum (fun _ e => e) = k + 1 := by
        intro b hb
        have hbShadow : b ∈
            A.biUnion (fun a => a.support.image fun i => a.update i (a i - 1)) := by
          simpa only [mms_shadow, mms_lower] using hBsubsetShadow hb
        exact shadow_mem_degree (k + 1) A b hbShadow hdegree
      have hCdegree : ∀ c ∈ C, c.sum (fun _ e => e) = k + 2 := by
        intro c hc
        exact hdegree c (hCsubset hc)
      let dB := mms_digits (k + 1) B.card
      let dC := mms_digits (k + 2) C.card
      have hdB : StrictMono dB := mms_digits_strict (k + 1) B.card (by omega)
      have hdC : StrictMono dC := mms_digits_strict (k + 2) C.card (by omega)
      have hBrep : B.card = ∑ i, Nat.choose (dB i) (i.1 + 1) :=
        mms_digits_sum (k + 1) B.card (by omega)
      have hCrep : C.card = ∑ i, Nat.choose (dC i) (i.1 + 1) :=
        mms_digits_sum (k + 2) C.card (by omega)
      have hBbound := ih (k + B.card) (by omega) k B dB hBdegree hdB hBrep rfl
      have hCbound := ih (k + 1 + C.card) (by omega) (k + 1) C dC hCdegree hdC hCrep rfl
      change mms_macaulay (k + 1) B.card ≤ (mms_shadow B).card at hBbound
      change mms_macaulay (k + 2) C.card ≤ (mms_shadow C).card at hCbound
      let R := (mms_shadow B).image (mms_raise p)
      have hRcard : R.card = (mms_shadow B).card := by
        dsimp [R]
        exact Finset.card_image_of_injective _ (mms_raise_injective p)
      have hdisjoint : Disjoint (mms_shadow C) R := by
        rw [Finset.disjoint_left]
        intro x hxC hxR
        have hxZero := mms_shadow_coord_zero p C hCzero hxC
        rw [Finset.mem_image] at hxR
        obtain ⟨y, hy, rfl⟩ := hxR
        simp [mms_raise] at hxZero
      have hRsubset : R ⊆ mms_shadow A := by
        dsimp [R, B]
        exact mms_raise_shadow_subset p A P hPsubset hPpos
      have hUnionSubset : mms_shadow C ∪ R ⊆ mms_shadow A := by
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact mms_shadow_mono hCsubset hx
        · exact hRsubset hx
      have hShadowSum : (mms_shadow C).card + (mms_shadow B).card ≤
          (mms_shadow A).card := by
        calc
          (mms_shadow C).card + (mms_shadow B).card =
              (mms_shadow C).card + R.card := by rw [hRcard]
          _ = (mms_shadow C ∪ R).card :=
            (Finset.card_union_of_disjoint hdisjoint).symm
          _ ≤ (mms_shadow A).card := Finset.card_le_card hUnionSubset
      rw [← mms_macaulay_eq (k + 2) A.card digits (by omega) hstrict hcard]
      change mms_macaulay (k + 2) A.card ≤ (mms_shadow A).card
      by_cases hlarge : mms_macaulay (k + 2) A.card ≤ B.card
      · exact hlarge.trans (Finset.card_le_card hBsubsetShadow)
      · have hsmall : B.card < mms_macaulay (k + 2) A.card := Nat.lt_of_not_ge hlarge
        have hnum := mms_split_ineq (k + 1) A.card B.card C.card (by omega)
          hcardSplit hsmall
        change mms_macaulay (k + 1) B.card + mms_macaulay (k + 2) C.card ≥
          mms_macaulay (k + 2) A.card at hnum
        omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hA
      subst hA
      have h0 : (0 : ℕ) = ∑ i, Nat.choose (digits i) (i.1 + 1) := by
        simpa using hcard
      rw [macaulay_empty (k + 1) digits hstrict h0]
      simp

end
end MetaMathlibExt
