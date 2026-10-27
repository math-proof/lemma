import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.CobhamGapTheorem
open MetaMathlibExt


namespace MetaMathlibExt

/--
[baseDigits_length_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
private lemma baseDigits_length_le {k : ℕ} (hk : 2 ≤ k) {r n : ℕ}
  (hn : n < k ^ r) : (baseDigits hk n).length ≤ r := by
  rw [baseDigits_length]
  by_cases hn0 : n = 0
  · subst n
    simp
  · rw [Nat.length_digits k n (by omega) hn0]
    have := (Nat.log_lt_iff_lt_pow (by omega) hn0).2 hn
    omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[paddedDigits_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
private lemma paddedDigits_length {k : ℕ} (hk : 2 ≤ k) {r n : ℕ}
  (hn : n < k ^ r) : (paddedDigits hk r n).length = r := by
  have hlen := baseDigits_length_le hk hn
  simp [paddedDigits, Nat.sub_add_cancel hlen]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseWordValue_replicate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
private lemma baseWordValue_replicate_zero {k r : ℕ} (hk : 2 ≤ k) :
  baseWordValue (List.replicate r (⟨0, by omega⟩ : Fin k)) = 0 := by
  induction r with
  | zero => simp [baseWordValue]
  | succ r ih =>
    rw [List.replicate_succ]
    simpa [baseWordValue] using ih

end MetaMathlibExt

namespace MetaMathlibExt

/--
[paddedDigits_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
private lemma paddedDigits_value {k : ℕ} (hk : 2 ≤ k) (r n : ℕ) :
  baseWordValue (paddedDigits hk r n) = n := by
  rw [paddedDigits, baseWordValue_append, baseWordValue_replicate_zero hk,
    zero_mul, zero_add, baseWordValue_baseDigits]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cobham_gap_theorem_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
lemma cobham_gap_theorem_general
  {k : ℕ}
  {x : ℕ → ℕ}
-- given
  (hx : StrictMono x)
  (hX : IsBaseRecognizable k (Set.range x)) :
-- imply
  Filter.limsup
    (fun i => ((x (i + 1) : ENNReal) / (x i : ENNReal)))
    Filter.atTop > 1 ∨
    ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C := by
-- proof
  classical
  have hk : 2 ≤ k := hX.1
  by_cases hbounded : ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C
  · exact Or.inr hbounded
  left
  have hgap : ∀ C : ℕ, ∃ i : ℕ, C < x (i + 1) - x i := by
    simpa only [not_exists, not_forall, not_le] using hbounded
  obtain ⟨_, q, hq, init, transition, accept, haccept⟩ := hX
  let gapIndex : ℕ → ℕ := fun r ↦ Classical.choose (hgap (2 * k ^ r))
  have hgapIndex (r : ℕ) :
    2 * k ^ r < x (gapIndex r + 1) - x (gapIndex r) :=
    Classical.choose_spec (hgap (2 * k ^ r))
  let blockPrefix : ℕ → ℕ := fun r ↦ x (gapIndex r) / k ^ r + 1
  have hpow (r : ℕ) : 0 < k ^ r := pow_pos (by omega) r
  have hprefix (r : ℕ) : 0 < blockPrefix r := by simp [blockPrefix]
  have hblock (r n : ℕ)
    (hnl : blockPrefix r * k ^ r ≤ n)
    (hnr : n < (blockPrefix r + 1) * k ^ r) : n ∉ Set.range x := by
    intro hn
    obtain ⟨j, rfl⟩ := hn
    have hleft : x (gapIndex r) < blockPrefix r * k ^ r := by
      change x (gapIndex r) < (x (gapIndex r) / k ^ r + 1) * k ^ r
      simpa [Nat.add_mul] using
        (Nat.lt_div_mul_add (a := x (gapIndex r)) (b := k ^ r) (hpow r))
    have hgap' : x (gapIndex r) + 2 * k ^ r < x (gapIndex r + 1) := by
      simpa [Nat.add_comm] using
        (Nat.lt_sub_iff_add_lt.mp (hgapIndex r))
    have hright : (blockPrefix r + 1) * k ^ r ≤ x (gapIndex r + 1) := by
      change (x (gapIndex r) / k ^ r + 1 + 1) * k ^ r ≤
        x (gapIndex r + 1)
      calc
        (x (gapIndex r) / k ^ r + 1 + 1) * k ^ r =
          x (gapIndex r) / k ^ r * k ^ r + 2 * k ^ r := by ring
        _ ≤ x (gapIndex r) + 2 * k ^ r :=
          Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
        _ ≤ x (gapIndex r + 1) := hgap'.le
    have hjlow : gapIndex r < j := (hx.lt_iff_lt).mp (hleft.trans_le hnl)
    have hjhigh : j < gapIndex r + 1 :=
      (hx.lt_iff_lt).mp (hnr.trans_le hright)
    omega
  let state : ℕ → Fin q := fun r ↦
    (baseDigits hk (blockPrefix r)).foldl transition init
  obtain ⟨repeatedState, hrepeated⟩ := Finite.exists_infinite_fiber state
  have hrepeatedSet : Set.Infinite {r : ℕ | state r = repeatedState} := by
    have hi : Set.Infinite (state ⁻¹' {repeatedState}) :=
      Set.infinite_coe_iff.mp hrepeated
    convert hi using 1
    ext r
    simp
  obtain ⟨r₀, hr₀, _⟩ := hrepeatedSet.exists_gt 0
  let fixedPrefix := blockPrefix r₀
  have hfixedPrefix : 0 < fixedPrefix := hprefix r₀
  have hstate₀ : state r₀ = repeatedState := hr₀
  have hfixedBlock (r n : ℕ) (hr : state r = repeatedState)
    (hnl : fixedPrefix * k ^ r ≤ n)
    (hnr : n < (fixedPrefix + 1) * k ^ r) : n ∉ Set.range x := by
    intro hn
    let remainder := n - fixedPrefix * k ^ r
    have hremainder : remainder < k ^ r := by
      dsimp [remainder]
      rw [Nat.sub_lt_iff_lt_add hnl]
      simpa [Nat.add_mul, Nat.add_comm] using hnr
    let suffix := paddedDigits hk r remainder
    have hsuffixLength : suffix.length = r := paddedDigits_length hk hremainder
    have hsuffixValue : baseWordValue suffix = remainder := paddedDigits_value hk r remainder
    have hfixedValue :
      baseWordValue (baseDigits hk fixedPrefix ++ suffix) = n := by
      rw [baseWordValue_append, baseWordValue_baseDigits, hsuffixLength,
        hsuffixValue]
      exact Nat.add_sub_of_le hnl
    have horiginalValue :
      baseWordValue (baseDigits hk (blockPrefix r) ++ suffix) =
        blockPrefix r * k ^ r + remainder := by
      rw [baseWordValue_append, baseWordValue_baseDigits, hsuffixLength,
        hsuffixValue]
    have hfixedCanonical :
      IsCanonicalBaseWord (baseDigits hk fixedPrefix ++ suffix) :=
      (isCanonicalBaseWord_baseDigits hk fixedPrefix).append
        (baseDigits_ne_nil hk hfixedPrefix.ne')
    have horiginalCanonical :
      IsCanonicalBaseWord (baseDigits hk (blockPrefix r) ++ suffix) :=
      (isCanonicalBaseWord_baseDigits hk (blockPrefix r)).append
        (baseDigits_ne_nil hk (hprefix r).ne')
    have hstates :
      (baseDigits hk fixedPrefix ++ suffix).foldl transition init =
        (baseDigits hk (blockPrefix r) ++ suffix).foldl transition init := by
      simp only [List.foldl_append]
      have : state r₀ = state r := hstate₀.trans hr.symm
      simpa [state, fixedPrefix] using congrArg
        (fun s ↦ suffix.foldl transition s) this
    have haccepted :
      accept ((baseDigits hk fixedPrefix ++ suffix).foldl transition init) = true :=
      (haccept _).2 ⟨hfixedCanonical, hfixedValue ▸ hn⟩
    have horiginalAccepted :
      accept ((baseDigits hk (blockPrefix r) ++ suffix).foldl
        transition init) = true := by
      rwa [← hstates]
    have horiginalMember : blockPrefix r * k ^ r + remainder ∈ Set.range x := by
      have hm := (haccept _).1 horiginalAccepted
      rwa [horiginalValue] at hm
    apply hblock r (blockPrefix r * k ^ r + remainder)
      (Nat.le_add_right _ _) _ horiginalMember
    calc
      blockPrefix r * k ^ r + remainder <
        blockPrefix r * k ^ r + k ^ r := Nat.add_lt_add_left hremainder _
      _ = (blockPrefix r + 1) * k ^ r := by ring
  let ratioBound : ENNReal :=
    ((fixedPrefix + 1 : ℕ) : ENNReal) / (fixedPrefix : ENNReal)
  have hfixedCastZero : (fixedPrefix : ENNReal) ≠ 0 := by
    exact_mod_cast hfixedPrefix.ne'
  have hfixedCastTop : (fixedPrefix : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top fixedPrefix
  have hratioBound : 1 < ratioBound := by
    change 1 < ((fixedPrefix + 1 : ℕ) : ENNReal) / (fixedPrefix : ENNReal)
    rw [← ENNReal.div_self hfixedCastZero hfixedCastTop]
    apply ENNReal.div_lt_div_right hfixedCastZero hfixedCastTop
    exact_mod_cast Nat.lt_succ_self fixedPrefix
  have hfrequent :
    ∃ᶠ i : ℕ in Filter.atTop,
      ratioBound ≤ (x (i + 1) : ENNReal) / (x i : ENNReal) := by
    rw [Filter.frequently_atTop]
    intro bound
    obtain ⟨r, hr, hrlarge⟩ := hrepeatedSet.exists_gt (x bound)
    have hpowLarge : x bound < k ^ r :=
      hrlarge.trans (Nat.lt_pow_self (by omega))
    have hpowFixed : k ^ r ≤ fixedPrefix * k ^ r := by
      exact Nat.le_mul_of_pos_left (k ^ r) hfixedPrefix
    have hboundLeft : x bound < fixedPrefix * k ^ r :=
      hpowLarge.trans_le hpowFixed
    have hleftRight : fixedPrefix * k ^ r < (fixedPrefix + 1) * k ^ r := by
      exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self fixedPrefix) (hpow r)
    have htExists : ∃ t : ℕ, (fixedPrefix + 1) * k ^ r ≤ x t := by
      refine ⟨(fixedPrefix + 1) * k ^ r, ?_⟩
      exact hx.id_le _
    let t := Nat.find htExists
    have ht : (fixedPrefix + 1) * k ^ r ≤ x t := Nat.find_spec htExists
    have hxzero : x 0 < (fixedPrefix + 1) * k ^ r := by
      exact (hx.monotone (Nat.zero_le bound)).trans_lt
        (hboundLeft.trans hleftRight)
    have htpos : 0 < t := by
      dsimp [t]
      rw [Nat.find_pos]
      exact not_le_of_gt hxzero
    let i := t - 1
    have hit : i + 1 = t := Nat.sub_add_cancel htpos
    have hitlt : i < t := by omega
    have hiprev : x i < (fixedPrefix + 1) * k ^ r := by
      have hmin := Nat.find_min htExists (m := i) (by simpa [t] using hitlt)
      have := hmin
      omega
    have hileft : x i < fixedPrefix * k ^ r := by
      by_contra hi
      exact hfixedBlock r (x i) hr (Nat.le_of_not_gt hi) hiprev ⟨i, rfl⟩
    have hinext : (fixedPrefix + 1) * k ^ r ≤ x (i + 1) := by
      simpa [hit] using ht
    have hibound : bound ≤ i := by
      have : bound < i + 1 :=
        (hx.lt_iff_lt).mp (hboundLeft.trans hleftRight |>.trans_le hinext)
      omega
    refine ⟨i, hibound, ?_⟩
    have hkCastZero : (k ^ r : ENNReal) ≠ 0 := by
      exact_mod_cast (hpow r).ne'
    have hkCastTop : (k ^ r : ENNReal) ≠ ⊤ :=
      by simpa only [Nat.cast_pow] using ENNReal.natCast_ne_top (k ^ r)
    have hscaled :
      (((fixedPrefix + 1) * k ^ r : ℕ) : ENNReal) /
        ((fixedPrefix * k ^ r : ℕ) : ENNReal) = ratioBound := by
      simp only [ratioBound, Nat.cast_mul, Nat.cast_pow]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENNReal.mul_div_mul_right (fixedPrefix + 1 : ENNReal)
          (fixedPrefix : ENNReal) hkCastZero hkCastTop)
    rw [← hscaled]
    apply ENNReal.div_le_div
    · exact_mod_cast hinext
    · exact_mod_cast hileft.le
  exact hratioBound.trans_le
    (Filter.le_limsup_of_frequently_le hfrequent)
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[cobham_gap_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamGapTheorem.lean)
-/
@[path]
lemma cobham_gap_theorem
  {k : ℕ}
  {x : ℕ → ℕ}
-- given
  (hx : StrictMono x)
  (hk : 2 ≤ k)
  (hX : IsBaseRecognizable k (Set.range x)) :
-- imply
  Filter.limsup
    (fun i => ((x (i + 1) : ENNReal) / (x i : ENNReal)))
    Filter.atTop > 1 ∨
    ∃ C : ℕ, ∀ i : ℕ, x (i + 1) - x i ≤ C :=
-- proof
  cobham_gap_theorem_general hx hX

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
