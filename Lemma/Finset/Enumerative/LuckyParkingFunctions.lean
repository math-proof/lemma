import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part12
open MetaMathlibExt


namespace MetaMathlibExt

/--
[park_card_eq_filter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma park_card_eq_filter (n : ℕ) :
  Fintype.card (Park n) =
    (Finset.univ.filter
      (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val)).card :=
  Fintype.card_subtype _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[marked_card_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma marked_card_eq_sum (n : ℕ) :
  Fintype.card (Marked n) =
    ∑ a ∈ Finset.univ.filter
      (fun a : Fin n → Fin n => Monotone a ∧ ∀ i, (a i).val ≤ i.val),
      (Finset.univ.filter (fun i : Fin n => a i = i)).card := by
  have h1 := Fintype.card_congr (markedEquivSigma n)
  rw [Fintype.card_coe] at h1
  rw [h1, Finset.card_sigma]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[marked_card_eq_fiber_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma marked_card_eq_fiber_sum (n : ℕ) :
  Fintype.card (Marked n) =
    ∑ i0 : Fin n,
      Fintype.card (Park i0.val) * Fintype.card (Park (n - i0.val)) := by
  have h1 := Fintype.card_congr (markedFiberEquiv n)
  rw [h1, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i0 _
  have h2 := Fintype.card_congr (fiberEquiv n i0)
  rw [h2, Fintype.card_prod]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[marked_no_small_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma marked_no_small_fixed (n : ℕ) (m : Marked n)
  (k : Fin (n + 1)) (hpos : 0 < k.val)
  (hlt : k.val < m.2.1.val + 1) : (embedMarked n m).1 k ≠ k := by
  obtain ⟨⟨a, ha⟩, ⟨i0, hi⟩⟩ := m
  have hlt' : k.val < i0.val + 1 := hlt
  intro heq
  have hval : ((embedMarked n ⟨⟨a, ha⟩, ⟨i0, hi⟩⟩).1 k).val = k.val :=
    congrArg Fin.val heq
  have h0 : k.val ≠ 0 := by
    omega
  have h1 : k.val - 1 < i0.val := by
    omega
  have hmem : k.val - 1 < n := by
    omega
  have hB : (markedFun n a i0 k).val = (a ⟨k.val - 1, hmem⟩).val := by
    simp only [markedFun, dite_eq_right h0, dite_eq_left h1]
  have hb := ha.2 ⟨k.val - 1, hmem⟩
  simp only [embedMarked] at hval
  simp only at hb
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[embedPlain_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma embedPlain_injective (n : ℕ) :
  Function.Injective (embedPlain n) := by
  intro a1 a2 heq
  obtain ⟨a1f, ha1⟩ := a1
  obtain ⟨a2f, ha2⟩ := a2
  apply Subtype.ext
  funext j
  apply Fin.ext
  have hk : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val ≠ 0 := by
    simp only
    omega
  have h1 : (plainFun n a1f ⟨j.val + 1, by omega⟩).val =
    (a1f ⟨(⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1, by omega⟩).val := by
    simp only [plainFun, dite_eq_right hk]
  have h2 : (plainFun n a2f ⟨j.val + 1, by omega⟩).val =
    (a2f ⟨(⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1, by omega⟩).val := by
    simp only [plainFun, dite_eq_right hk]
  have hval :
    ((embedPlain n ⟨a1f, ha1⟩).1 ⟨j.val + 1, by omega⟩).val =
      ((embedPlain n ⟨a2f, ha2⟩).1 ⟨j.val + 1, by omega⟩).val := by
    rw [heq]
  simp only [embedPlain] at hval
  rwa [h1, h2] at hval

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unplainFun_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unplainFun_mono (n : ℕ) (b : Park (n + 1))
  (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
  Monotone (unplainFun n b hNo) := by
  intro j1 j2 hle
  have hle' : j1.val ≤ j2.val := Fin.le_def.mp hle
  have hmon : b.1 ⟨j1.val + 1, by omega⟩ ≤ b.1 ⟨j2.val + 1, by omega⟩ := by
    apply b.2.1
    rw [Fin.le_def]
    simp only
    omega
  rw [Fin.le_def]
  exact Fin.le_def.mp hmon

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unplainFun_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unplainFun_bound (n : ℕ) (b : Park (n + 1))
  (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) (j : Fin n) :
  (unplainFun n b hNo j).val ≤ j.val := by
  have hpos : 0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
    simp only
    omega
  have hNe := hNo ⟨j.val + 1, by omega⟩ hpos
  have hb := b.2.2 ⟨j.val + 1, by omega⟩
  simp only at hb
  have hval_ne :
    (b.1 ⟨j.val + 1, by omega⟩).val ≠
      (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
    intro hEq
    exact hNe (Fin.ext hEq)
  simp only at hval_ne
  change (b.1 ⟨j.val + 1, by omega⟩).val ≤ j.val
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unmarkedFun_val_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unmarkedFun_val_of_lt (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
  (j : Fin n) (h : j.val < i0.val) :
  (unmarkedFun n b i0 j).val = (b.1 ⟨j.val + 1, by omega⟩).val := by
  simp only [unmarkedFun, dite_eq_left h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unmarkedFun_val_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unmarkedFun_val_of_ge (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
  (j : Fin n) (h : ¬ j.val < i0.val) :
  (unmarkedFun n b i0 j).val =
    (b.1 ⟨j.val + 1, by omega⟩).val - 1 := by
  simp only [unmarkedFun, dite_eq_right h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unmarkedFun_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unmarkedFun_mono (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
  (hfix : b.1 ⟨i0.val + 1, by omega⟩ = ⟨i0.val + 1, by omega⟩) :
  Monotone (unmarkedFun n b i0) := by
  intro j1 j2 hle
  have hle' : j1.val ≤ j2.val := Fin.le_def.mp hle
  by_cases h1 : j1.val < i0.val
  · by_cases h2 : j2.val < i0.val
    · rw [Fin.le_def, unmarkedFun_val_of_lt n b i0 j1 h1,
      unmarkedFun_val_of_lt n b i0 j2 h2]
      have hmon : b.1 ⟨j1.val + 1, by omega⟩ ≤
        b.1 ⟨j2.val + 1, by omega⟩ := by
        apply b.2.1
        rw [Fin.le_def]
        simp only
        omega
      exact Fin.le_def.mp hmon
    · rw [Fin.le_def, unmarkedFun_val_of_lt n b i0 j1 h1,
      unmarkedFun_val_of_ge n b i0 j2 h2]
      have hb1 := b.2.2 ⟨j1.val + 1, by omega⟩
      simp only at hb1
      have hleK : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) ≤
        ⟨j2.val + 1, by omega⟩ := by
        rw [Fin.le_def]
        simp only
        omega
      have hmon : b.1 ⟨i0.val + 1, by omega⟩ ≤
        b.1 ⟨j2.val + 1, by omega⟩ := b.2.1 hleK
      have hfixV : (b.1 ⟨i0.val + 1, by omega⟩).val = i0.val + 1 :=
        congrArg Fin.val hfix
      have hle2 := Fin.le_def.mp hmon
      omega
  · by_cases h2 : j2.val < i0.val
    · have hcon : j1.val < i0.val := lt_of_le_of_lt hle' h2
      exact absurd hcon h1
    · rw [Fin.le_def, unmarkedFun_val_of_ge n b i0 j1 h1,
      unmarkedFun_val_of_ge n b i0 j2 h2]
      have hmon : b.1 ⟨j1.val + 1, by omega⟩ ≤
        b.1 ⟨j2.val + 1, by omega⟩ := by
        apply b.2.1
        rw [Fin.le_def]
        simp only
        omega
      have h := Fin.le_def.mp hmon
      omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unmarkedFun_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unmarkedFun_bound (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
  (hmin : ∀ k : Fin (n + 1), 0 < k.val → k.val < i0.val + 1 → b.1 k ≠ k)
  (j : Fin n) : (unmarkedFun n b i0 j).val ≤ j.val := by
  by_cases h : j.val < i0.val
  · rw [unmarkedFun_val_of_lt n b i0 j h]
    have hb := b.2.2 ⟨j.val + 1, by omega⟩
    simp only at hb
    have hpos : 0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
      simp only
      omega
    have hlt : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val < i0.val + 1 := by
      simp only
      omega
    have hNe := hmin ⟨j.val + 1, by omega⟩ hpos hlt
    have hval_ne : (b.1 ⟨j.val + 1, by omega⟩).val ≠
      (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
      intro hEq
      exact hNe (Fin.ext hEq)
    simp only at hval_ne
    omega
  · rw [unmarkedFun_val_of_ge n b i0 j h]
    have hb := b.2.2 ⟨j.val + 1, by omega⟩
    simp only at hb
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[unmarkedFun_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma unmarkedFun_fixed (n : ℕ) (b : Park (n + 1)) (i0 : Fin n)
  (hfix : b.1 ⟨i0.val + 1, by omega⟩ = ⟨i0.val + 1, by omega⟩) :
  unmarkedFun n b i0 i0 = i0 := by
  apply Fin.ext
  have hneg : ¬ i0.val < i0.val := lt_irrefl _
  rw [unmarkedFun_val_of_ge n b i0 i0 hneg]
  have hfixV : (b.1 ⟨i0.val + 1, by omega⟩).val = i0.val + 1 :=
    congrArg Fin.val hfix
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[park_zero_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma park_zero_card : Fintype.card (Park 0) = 1 := by
  have huniq : Unique (Park 0) :=
    ⟨⟨fun i => Fin.elim0 i, fun a => Fin.elim0 a, fun i => Fin.elim0 i⟩,
      fun a => Subtype.ext (funext fun i => Fin.elim0 i)⟩
  exact @Fintype.card_unique _ huniq _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ratio_of_catalan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma ratio_of_catalan (n : ℕ) (hn : 0 < n)
  (Cn : ℕ) (hCn : 0 < Cn)
  (h1 : (n + 1) * Cn = n.centralBinom)
  (h2 : (n + 2) * (catalan (n + 1)) = (n + 1).centralBinom)
  (h3 : (n + 1) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom)
  (M : ℕ)
  (hM : catalan (n + 1) = Cn + M) :
  (M : ℚ) / (Cn : ℚ) = ((3 : ℚ) * n) / (n + 2) := by
  have hCn' : (Cn : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hCn
  have hn2 : ((n : ℚ) + 2) ≠ 0 := by positivity
  have key : (n + 2) * catalan (n + 1) = 2 * (2 * n + 1) * Cn := by
    have e1 : (n+1) * ((n+2) * catalan (n+1)) = (n+1) * (2 * (2*n+1) * Cn) := by
      calc (n+1) * ((n+2) * catalan (n+1))
        = (n+2) * catalan (n+1) * (n+1) := by ring
        _ = (n+1).centralBinom * (n+1) := by rw [h2]
        _ = (n+1) * (n+1).centralBinom := by ring
        _ = 2 * (2*n+1) * n.centralBinom := h3
        _ = 2 * (2*n+1) * ((n+1) * Cn) := by rw [h1]
        _ = (n+1) * (2 * (2*n+1) * Cn) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos n) e1
  have keyQ : ((n : ℚ) + 2) * (catalan (n+1) : ℚ) = 2 * (2 * n + 1) * (Cn : ℚ) := by
    exact_mod_cast key
  have hMQ : (M : ℚ) = (catalan (n+1) : ℚ) - (Cn : ℚ) := by
    have hcast : (catalan (n+1) : ℚ) = (Cn : ℚ) + (M : ℚ) := by exact_mod_cast hM
    linarith
  rw [hMQ]
  field_simp
  linarith [keyQ]

end MetaMathlibExt

/--
[expected_lucky_spots_weakly_increasing_parking_functions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean)
-/
@[path]
private lemma expected_lucky_spots_weakly_increasing_parking_functions_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  let parkingFunctions := by
-- proof
  apply MetaMathlibExt.expected_lucky_spots_weakly_increasing_parking_functions n hn


-- created on 2026-10-20
-- updated on 2026-10-26
