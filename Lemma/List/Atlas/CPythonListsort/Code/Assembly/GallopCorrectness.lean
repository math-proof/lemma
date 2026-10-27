import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.GallopCorrectness
open CPythonListsort


namespace CPythonListsort

/--
[gallopSortedRange_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopSortedRange_of_sorted
  {κ : Type u}
  {ν : Type v}
  {lt : BoolComparator κ}
  {source : GallopKeySource κ ν}
  {n : Nat}
  {keys : Array κ}
-- given
  (hagrees : GallopKeyArrayAgreement source n keys)
  (hsorted : Sorted lt keys) :
-- imply
  GallopSortedRange lt source n := by
-- proof
  obtain ⟨hsize, hagrees⟩ := hagrees
  intro i j hi hj hij earlier later heariler hlater
  obtain ⟨sourceEarlier, hsourceEarlier, hkeyEarlier⟩ := hagrees i hi
  obtain ⟨sourceLater, hsourceLater, hkeyLater⟩ := hagrees j hj
  have hsourceEarlierEq : sourceEarlier = earlier :=
    Option.some.inj (hsourceEarlier.symm.trans heariler)
  have hsourceLaterEq : sourceLater = later :=
    Option.some.inj (hsourceLater.symm.trans hlater)
  subst sourceEarlier
  subst sourceLater
  have hiKeys : i < keys.size := by omega
  have hjKeys : j < keys.size := by omega
  have hgetEarlier : keys[i]? = some keys[i] := by simp [hiKeys]
  have hgetLater : keys[j]? = some keys[j] := by simp [hjKeys]
  have hearlierKey : earlier.key = keys[i] :=
    Option.some.inj (hkeyEarlier.symm.trans hgetEarlier)
  have hlaterKey : later.key = keys[j] :=
    Option.some.inj (hkeyLater.symm.trans hgetLater)
  have hnot := (sorted_iff_no_later_precedes lt keys).1 hsorted
    i j hiKeys hjKeys hij
  apply Bool.eq_false_of_not_eq_true
  intro hcompare
  apply hnot
  simpa [hearlierKey, hlaterKey] using hcompare

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[read_false_of_not_before](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma read_false_of_not_before
  (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
  {i : Nat} {entry : SortSliceEntry κ ν}
  (hread : source.read? (Int.ofNat i) = some entry)
  (hcompare : ¬lt entry.key key = true) :
  ¬GallopBefore lt source key i := by
  rintro ⟨other, hother, hotherCompare⟩
  have : other = entry := Option.some.inj (hother.symm.trans hread)
  subst other
  exact hcompare hotherCompare

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[read_not_after_of_dual_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma read_not_after_of_dual_true
  (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
  {i : Nat} {entry : SortSliceEntry κ ν}
  (hread : source.read? (Int.ofNat i) = some entry)
  (hcompare : gallopComparatorDual lt entry.key key = true) :
  ¬GallopAfter lt source key i := by
  have hfalse : lt key entry.key = false := by
    simpa [gallopComparatorDual] using hcompare
  rintro ⟨other, hother, hotherCompare⟩
  have : other = entry := Option.some.inj (hother.symm.trans hread)
  subst other
  simp [hfalse] at hotherCompare

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[read_after_of_dual_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma read_after_of_dual_false
  (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
  {i : Nat} {entry : SortSliceEntry κ ν}
  (hread : source.read? (Int.ofNat i) = some entry)
  (hcompare : ¬gallopComparatorDual lt entry.key key = true) :
  GallopAfter lt source key i := by
  refine ⟨entry, hread, ?_⟩
  cases hvalue : lt key entry.key <;>
    simp [gallopComparatorDual, hvalue] at hcompare ⊢

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftBinaryFromSource_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopLeftBinaryFromSource_partition
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (lower upper n : Nat)
  (hvalid : source.ValidRange n)
  (hprefix : GallopPrefix (GallopBefore lt source key) n)
  (hlowerUpper : lower ≤ upper) (hupper : upper ≤ n)
  (hbefore : ∀ i, i < lower → GallopBefore lt source key i)
  (hafter : ∀ i, upper ≤ i → i < n → ¬GallopBefore lt source key i)
  (hbudget : upper - lower ≤ fuel) :
  ∃ result,
    gallopLeftBinaryFromSource? fuel lt source key lower upper = some result ∧
    result.fuelExhausted = false ∧
    GallopPartition (GallopBefore lt source key) n result.index := by
  induction fuel generalizing lower upper with
  | zero =>
    have heq : lower = upper := by omega
    subst upper
    refine ⟨⟨lower, false⟩, ?_, rfl, hupper, hbefore, hafter⟩
    simp [gallopLeftBinaryFromSource?]
  | succ fuel ih =>
    by_cases hsearch : lower < upper
    · let middle := lower + (upper - lower) / 2
      have hlowerMiddle : lower ≤ middle := by
        dsimp [middle]
        omega
      have hmiddleUpper : middle < upper := by
        dsimp [middle]
        omega
      have hmiddleN : middle < n := by omega
      obtain ⟨entry, hread⟩ := source.read_eq_some hvalid hmiddleN
      have hread' :
        source.read? (Int.ofNat (lower + (upper - lower) / 2)) =
          some entry := by
        simpa only [middle] using hread
      by_cases hcompare : iflt lt entry.key key = true
      · have hcompareRaw : lt entry.key key = true := by
        simpa only [iflt] using hcompare
        have hmiddleBefore : GallopBefore lt source key middle :=
          ⟨entry, hread, hcompareRaw⟩
        have hbefore' :
          ∀ i, i < middle + 1 → GallopBefore lt source key i := by
          intro i hi
          by_cases him : i = middle
          · simpa [him] using hmiddleBefore
          · exact hprefix i middle (by omega) hmiddleN hmiddleBefore
        have hbudget' : upper - (middle + 1) ≤ fuel := by
          dsimp [middle]
          omega
        rcases ih (middle + 1) upper (by omega) hupper hbefore' hafter
          hbudget' with ⟨result, hresult, hfuel, hpartition⟩
        refine ⟨result, ?_, hfuel, hpartition⟩
        rw [gallopLeftBinaryFromSource?, if_pos hsearch]
        simp only [gallopBindOptionAcross]
        rw [hread']
        simp only [if_pos hcompare]
        simpa only [middle] using hresult
      · have hcompareRaw : ¬lt entry.key key = true := by
        simpa only [iflt] using hcompare
        have hmiddleNot : ¬GallopBefore lt source key middle :=
          read_false_of_not_before lt source key hread hcompareRaw
        have hafter' :
          ∀ i, middle ≤ i → i < n → ¬GallopBefore lt source key i := by
          intro i hmi hin hpred
          by_cases him : i = middle
          · exact hmiddleNot (him ▸ hpred)
          · exact hmiddleNot (hprefix middle i (by omega) hin hpred)
        have hbudget' : middle - lower ≤ fuel := by
          dsimp [middle]
          omega
        rcases ih lower middle hlowerMiddle (by omega) hbefore hafter'
          hbudget' with ⟨result, hresult, hfuel, hpartition⟩
        refine ⟨result, ?_, hfuel, hpartition⟩
        rw [gallopLeftBinaryFromSource?, if_pos hsearch]
        simp only [gallopBindOptionAcross]
        rw [hread']
        simp only [if_neg hcompare]
        simpa only [middle] using hresult
    · have heq : lower = upper := by omega
      subst upper
      refine ⟨⟨lower, false⟩, ?_, rfl, hupper, hbefore, hafter⟩
      simp [gallopLeftBinaryFromSource?]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftRightExponential_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopLeftRightExponential_partition
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset n : Nat)
  (hvalid : source.ValidRange n)
  (hprefix : GallopPrefix (GallopBefore lt source key) n)
  (hwindow : hint + maxOffset = n) (hnmax : n ≤ PY_LIST_MAX)
  (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
  (hlastMax : lastOffset < maxOffset)
  (hbudget : maxOffset ≤ fuel + offset)
  (hbefore : ∀ i, i < hint + lastOffset + 1 →
    GallopBefore lt source key i) :
  ∃ result,
    gallopLeftRightExponentialFromSource? fuel lt source key hint maxOffset
      lastOffset offset = some result ∧
    result.fuelExhausted = false ∧
    result.lastOffset < result.offset ∧
    result.lastOffset < maxOffset ∧
    (∀ i, i < hint + result.lastOffset + 1 →
      GallopBefore lt source key i) ∧
    (∀ i, hint + min result.offset maxOffset ≤ i → i < n →
      ¬GallopBefore lt source key i) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    have hstop : ¬offset < maxOffset := by omega
    refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset, hlastMax,
      hbefore, ?_⟩
    · simp [gallopLeftRightExponentialFromSource?, hstop]
    · intro i hi hin
      change hint + min offset maxOffset ≤ i at hi
      have : hint + min offset maxOffset = n := by
        rwa [Nat.min_eq_right (by omega)]
      omega
  | succ fuel ih =>
    by_cases hprobe : offset < maxOffset
    · have hindex : hint + offset < n := by omega
      obtain ⟨entry, hread⟩ := source.read_eq_some hvalid hindex
      have hread' :
        source.read? (Int.ofNat hint + Int.ofNat offset) = some entry := by
        simpa using hread
      by_cases hcompare : iflt lt entry.key key = true
      · have hguard := gallop_doubling_guard hprobe (by omega : maxOffset ≤ n)
        hnmax
        have hcompareRaw : lt entry.key key = true := by
          simpa only [iflt] using hcompare
        have hpoint : GallopBefore lt source key (hint + offset) :=
          ⟨entry, hread, hcompareRaw⟩
        have hbefore' : ∀ i, i < hint + offset + 1 →
          GallopBefore lt source key i := by
          intro i hi
          by_cases hieq : i = hint + offset
          · simpa [hieq] using hpoint
          · exact hprefix i (hint + offset) (by omega) hindex hpoint
        rcases ih offset (2 * offset + 1) (by omega) (by omega) hprobe
          (by omega) hbefore' with
          ⟨result, hresult, hfuel, horder, hlast, hbeforeResult,
            hafterResult⟩
        refine ⟨result, ?_, hfuel, horder, hlast, hbeforeResult,
          hafterResult⟩
        rw [gallopLeftRightExponentialFromSource?, if_pos hprobe]
        simp only [gallopBindOptionAcross]
        rw [hread]
        simp only [if_pos hcompare, if_pos hguard]
        exact hresult
      · have hcompareRaw : ¬lt entry.key key = true := by
        simpa only [iflt] using hcompare
        have hnot : ¬GallopBefore lt source key (hint + offset) :=
          read_false_of_not_before lt source key hread hcompareRaw
        refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
          hlastMax, hbefore, ?_⟩
        · rw [gallopLeftRightExponentialFromSource?, if_pos hprobe]
          simp only [gallopBindOptionAcross]
          rw [hread]
          simp only [if_neg hcompare]
        · intro i hi hin hpred
          have hcap : min offset maxOffset = offset := Nat.min_eq_left (Nat.le_of_lt hprobe)
          rw [hcap] at hi
          by_cases hieq : i = hint + offset
          · exact hnot (hieq ▸ hpred)
          · exact hnot (hprefix (hint + offset) i (by omega) hin hpred)
    · refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
      hlastMax, hbefore, ?_⟩
      · simp [gallopLeftRightExponentialFromSource?, hprobe]
      · intro i hi hin
        have hcap : min offset maxOffset = maxOffset := Nat.min_eq_right (by omega)
        rw [hcap, hwindow] at hi
        omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftLeftExponential_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopLeftLeftExponential_partition
  (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (key : κ) (hint maxOffset lastOffset offset n : Nat)
  (hvalid : source.ValidRange n)
  (hprefix : GallopPrefix (GallopBefore lt source key) n)
  (hmax : maxOffset = hint + 1) (hnmax : n ≤ PY_LIST_MAX)
  (hhint : hint < n)
  (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
  (hlastMax : lastOffset < maxOffset)
  (hbudget : maxOffset ≤ fuel + offset)
  (hafter : ∀ i, hint - lastOffset ≤ i → i < n →
    ¬GallopBefore lt source key i) :
  ∃ result,
    gallopLeftLeftExponentialFromSource? fuel lt source key hint maxOffset
      lastOffset offset = some result ∧
    result.fuelExhausted = false ∧
    result.lastOffset < result.offset ∧
    result.lastOffset < maxOffset ∧
    (∀ i, i < hint + 1 - min result.offset maxOffset →
      GallopBefore lt source key i) ∧
    (∀ i, hint - result.lastOffset ≤ i → i < n →
      ¬GallopBefore lt source key i) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
    have hstop : ¬offset < maxOffset := by omega
    refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset, hlastMax,
      ?_, hafter⟩
    · simp [gallopLeftLeftExponentialFromSource?, hstop]
    · intro i hi
      have hcap : min offset maxOffset = maxOffset := Nat.min_eq_right (by omega)
      rw [hcap, hmax] at hi
      omega
  | succ fuel ih =>
    by_cases hprobe : offset < maxOffset
    · have hoffsetHint : offset ≤ hint := by omega
      have hindex : hint - offset < n := by omega
      have hindexEq :
        Int.ofNat hint - Int.ofNat offset = Int.ofNat (hint - offset) := by
        exact (Int.ofNat_sub hoffsetHint).symm
      obtain ⟨entry, hreadNat⟩ := source.read_eq_some hvalid hindex
      have hread : source.read? (Int.ofNat hint - Int.ofNat offset) =
        some entry := by rw [hindexEq]; exact hreadNat
      by_cases hcompare : iflt lt entry.key key = true
      · have hcompareRaw : lt entry.key key = true := by
        simpa only [iflt] using hcompare
        have hpoint : GallopBefore lt source key (hint - offset) :=
          ⟨entry, hreadNat, hcompareRaw⟩
        have hcap : min offset maxOffset = offset := Nat.min_eq_left (by omega)
        refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
          hlastMax, ?_, hafter⟩
        · rw [gallopLeftLeftExponentialFromSource?, if_pos hprobe]
          simp only [gallopBindOptionAcross]
          rw [hread]
          simp only [if_pos hcompare]
        · intro i hi
          rw [hcap] at hi
          by_cases hieq : i = hint - offset
          · simpa [hieq] using hpoint
          · exact hprefix i (hint - offset) (by omega) hindex hpoint
      · have hguard := gallop_doubling_guard hprobe (by omega : maxOffset ≤ n)
        hnmax
        have hcompareRaw : ¬lt entry.key key = true := by
          simpa only [iflt] using hcompare
        have hnot : ¬GallopBefore lt source key (hint - offset) :=
          read_false_of_not_before lt source key hreadNat hcompareRaw
        have hafter' : ∀ i, hint - offset ≤ i → i < n →
          ¬GallopBefore lt source key i := by
          intro i hii hin hpred
          by_cases hieq : i = hint - offset
          · exact hnot (hieq ▸ hpred)
          · exact hnot (hprefix (hint - offset) i (by omega) hin hpred)
        rcases ih offset (2 * offset + 1) (by omega) (by omega) hprobe
          (by omega) hafter' with
          ⟨result, hresult, hfuel, horder, hlast, hbeforeResult,
            hafterResult⟩
        refine ⟨result, ?_, hfuel, horder, hlast, hbeforeResult,
          hafterResult⟩
        rw [gallopLeftLeftExponentialFromSource?, if_pos hprobe]
        simp only [gallopBindOptionAcross]
        rw [hread]
        simp only [if_neg hcompare, if_pos hguard]
        exact hresult
    · refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
      hlastMax, ?_, hafter⟩
      · simp [gallopLeftLeftExponentialFromSource?, hprobe]
      · intro i hi
        have hcap : min offset maxOffset = maxOffset := Nat.min_eq_right (by omega)
        rw [hcap, hmax] at hi
        omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopLeftFromSource_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopLeftFromSource_partition
  (state : MergeState κ ν) (source : GallopKeySource κ ν)
  (key : κ) (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hprefix : GallopPrefix (GallopBefore state.key_compare source key) n)
  (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
  ∃ result,
    gallopLeftFromSource? state source key n hint = some result ∧
    result.fuelExhausted = false ∧
    GallopPartition (GallopBefore state.key_compare source key) n result.index := by
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  obtain ⟨hinted, hhinted⟩ := source.read_eq_some hvalid hhint
  by_cases hcompare : iflt state.key_compare hinted.key key = true
  · have hcompareRaw : state.key_compare hinted.key key = true := by
    simpa only [iflt] using hcompare
    have hhintedBefore :
      GallopBefore state.key_compare source key hint :=
      ⟨hinted, hhinted, hcompareRaw⟩
    have hbefore : ∀ i, i < hint + 1 →
      GallopBefore state.key_compare source key i := by
      intro i hi
      by_cases hieq : i = hint
      · simpa [hieq] using hhintedBefore
      · exact hprefix i hint (by omega) hhint hhintedBefore
    rcases gallopLeftRightExponential_partition (n + 1) state.key_compare
      source key hint (n - hint) 0 1 n hvalid hprefix (by omega) hnmax
      (by omega) (by omega) (by omega) (by omega) hbefore with
      ⟨exponential, hexponential, hexponentialFuel, hexponentialOrder,
        hexponentialMax, hbeforeWindow, hafterWindow⟩
    let capped := min exponential.offset (n - hint)
    let lower := hint + exponential.lastOffset + 1
    let upper := hint + capped
    have hlowerUpper : lower ≤ upper := by
      dsimp [lower, upper, capped]
      omega
    have hupper : upper ≤ n := by
      dsimp [upper, capped]
      omega
    have hbudget : upper - lower ≤ n + 1 := by omega
    rcases gallopLeftBinaryFromSource_partition (n + 1) state.key_compare
      source key lower upper n hvalid hprefix hlowerUpper hupper
      (by simpa [lower, Nat.add_assoc] using hbeforeWindow)
      (by simpa [upper, capped] using hafterWindow) hbudget with
      ⟨result, hbinary, hresultFuel, hpartition⟩
    have hfinish :
      finishGallopLeftFromSource? (n + 1) state.key_compare source key n
        (Int.ofNat exponential.lastOffset + Int.ofNat hint)
        (Int.ofNat capped + Int.ofNat hint) false =
        gallopLeftBinaryFromSource? (n + 1) state.key_compare source key
          lower upper := by
      unfold finishGallopLeftFromSource?
      have houter :
        (-1 : Int) ≤ Int.ofNat exponential.lastOffset + Int.ofNat hint ∧
        Int.ofNat exponential.lastOffset + Int.ofNat hint <
          Int.ofNat capped + Int.ofNat hint ∧
        Int.ofNat capped + Int.ofNat hint ≤ Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        dsimp [capped]
        omega
      rw [if_pos houter]
      have hinner :
        0 ≤ Int.ofNat exponential.lastOffset + Int.ofNat hint + 1 ∧
        0 ≤ Int.ofNat capped + Int.ofNat hint := by
        constructor <;> omega
      rw [if_pos hinner]
      have hlowerInt :
        (Int.ofNat exponential.lastOffset + Int.ofNat hint + 1).toNat =
          lower := by
        simp only [Int.ofNat_eq_natCast]
        dsimp [lower]
        omega
      have hupperInt :
        (Int.ofNat capped + Int.ofNat hint).toNat = upper := by
        simp only [Int.ofNat_eq_natCast]
        dsimp [upper]
        omega
      simp
      have hlowerInt' :
        (((exponential.lastOffset : Int) + (hint : Int) + 1).toNat) =
          lower := by simpa only [Int.ofNat_eq_natCast] using hlowerInt
      have hupperInt' :
        (((capped : Int) + (hint : Int)).toNat) = upper := by
        simpa only [Int.ofNat_eq_natCast] using hupperInt
      congr 2
    refine ⟨result, ?_, hresultFuel, hpartition⟩
    rw [gallopLeftFromSource?, if_pos hinput]
    simp only [gallopBindOptionAcross, hhinted, if_pos hcompare,
      hexponential]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [hexponentialFuel]
    change finishGallopLeftFromSource? (n + 1) state.key_compare source key n
      (Int.ofNat exponential.lastOffset + Int.ofNat hint)
      (Int.ofNat capped + Int.ofNat hint) false = some result
    rwa [hfinish]
  · have hcompareRaw : ¬state.key_compare hinted.key key = true := by
    simpa only [iflt] using hcompare
    have hhintedNot :
      ¬GallopBefore state.key_compare source key hint :=
      read_false_of_not_before state.key_compare source key hhinted hcompareRaw
    have hafter : ∀ i, hint ≤ i → i < n →
      ¬GallopBefore state.key_compare source key i := by
      intro i hii hin hpred
      by_cases hieq : i = hint
      · exact hhintedNot (hieq ▸ hpred)
      · exact hhintedNot (hprefix hint i (by omega) hin hpred)
    rcases gallopLeftLeftExponential_partition (n + 1) state.key_compare
      source key hint (hint + 1) 0 1 n hvalid hprefix rfl hnmax hhint
      (by omega) (by omega) (by omega) (by omega) hafter with
      ⟨exponential, hexponential, hexponentialFuel, hexponentialOrder,
        hexponentialMax, hbeforeWindow, hafterWindow⟩
    let capped := min exponential.offset (hint + 1)
    let lower := hint + 1 - capped
    let upper := hint - exponential.lastOffset
    have hlowerUpper : lower ≤ upper := by
      dsimp [lower, upper, capped]
      omega
    have hupper : upper ≤ n := by
      dsimp [upper]
      omega
    have hbudget : upper - lower ≤ n + 1 := by omega
    rcases gallopLeftBinaryFromSource_partition (n + 1) state.key_compare
      source key lower upper n hvalid hprefix hlowerUpper hupper
      (by simpa [lower] using hbeforeWindow)
      (by simpa [upper] using hafterWindow) hbudget with
      ⟨result, hbinary, hresultFuel, hpartition⟩
    have hcapped : capped ≤ hint + 1 := by
      exact Nat.min_le_right _ _
    have hlast : exponential.lastOffset ≤ hint := by omega
    have hlowerInt :
      (Int.ofNat hint - Int.ofNat capped + 1).toNat = lower := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [lower]
      omega
    have hupperInt :
      (Int.ofNat hint - Int.ofNat exponential.lastOffset).toNat = upper := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [upper]
      omega
    have hfinish :
      finishGallopLeftFromSource? (n + 1) state.key_compare source key n
        (Int.ofNat hint - Int.ofNat capped)
        (Int.ofNat hint - Int.ofNat exponential.lastOffset) false =
        gallopLeftBinaryFromSource? (n + 1) state.key_compare source key
          lower upper := by
      unfold finishGallopLeftFromSource?
      have houter :
        (-1 : Int) ≤ Int.ofNat hint - Int.ofNat capped ∧
        Int.ofNat hint - Int.ofNat capped <
          Int.ofNat hint - Int.ofNat exponential.lastOffset ∧
        Int.ofNat hint - Int.ofNat exponential.lastOffset ≤ Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [if_pos houter]
      have hinner :
        0 ≤ Int.ofNat hint - Int.ofNat capped + 1 ∧
        0 ≤ Int.ofNat hint - Int.ofNat exponential.lastOffset := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [if_pos hinner]
      simp
      have hlowerInt' :
        (((hint : Int) - (capped : Int) + 1).toNat) = lower := by
        simpa only [Int.ofNat_eq_natCast] using hlowerInt
      have hupperInt' :
        (((hint : Int) - (exponential.lastOffset : Int)).toNat) = upper := by
        simpa only [Int.ofNat_eq_natCast] using hupperInt
      congr 2
    refine ⟨result, ?_, hresultFuel, hpartition⟩
    rw [gallopLeftFromSource?, if_pos hinput]
    simp only [gallopBindOptionAcross, hhinted, if_neg hcompare,
      hexponential]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [hexponentialFuel]
    change finishGallopLeftFromSource? (n + 1) state.key_compare source key n
      (Int.ofNat hint - Int.ofNat capped)
      (Int.ofNat hint - Int.ofNat exponential.lastOffset) false = some result
    rwa [hfinish]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopBefore_prefix_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopBefore_prefix_of_sorted
  (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ) (n : Nat)
  (hvalid : source.ValidRange n) (horder : BoolStrictWeakOrder lt)
  (hsorted : GallopSortedRange lt source n) :
  GallopPrefix (GallopBefore lt source key) n := by
  intro i j hij hj hjBefore
  obtain ⟨later, hlater, hlaterKey⟩ := hjBefore
  obtain ⟨earlier, heariler⟩ := source.read_eq_some hvalid (by omega : i < n)
  have hlaterEarlierFalse :=
    hsorted i j (by omega) hj hij earlier later heariler hlater
  have hlaterEarlier : ¬lt later.key earlier.key = true := by
    simp [hlaterEarlierFalse]
  by_cases hearilerKey : lt earlier.key key = true
  · exact ⟨earlier, heariler, hearilerKey⟩
  · by_cases hearilerLater : lt earlier.key later.key = true
    · exact False.elim (hearilerKey
      (horder.trans earlier.key later.key key hearilerLater hlaterKey))
    · by_cases hkeyEarlier : lt key earlier.key = true
      · exact False.elim (hlaterEarlier
        (horder.trans later.key key earlier.key hlaterKey hkeyEarlier))
      · have hkeyEarlierIncomp :
        ¬lt key earlier.key = true ∧ ¬lt earlier.key key = true :=
        ⟨hkeyEarlier, hearilerKey⟩
        have hearilerLaterIncomp :
          ¬lt earlier.key later.key = true ∧
            ¬lt later.key earlier.key = true :=
          ⟨hearilerLater, hlaterEarlier⟩
        have hkeyLaterIncomp := horder.incomp_trans key earlier.key later.key
          hkeyEarlierIncomp hearilerLaterIncomp
        exact False.elim (hkeyLaterIncomp.2 hlaterKey)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopAfter_suffix_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopAfter_suffix_of_sorted
  (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ) (n : Nat)
  (hvalid : source.ValidRange n) (horder : BoolStrictWeakOrder lt)
  (hsorted : GallopSortedRange lt source n) :
  ∀ i j, i < j → j < n → GallopAfter lt source key i →
    GallopAfter lt source key j := by
  intro i j hij hj hiAfter
  obtain ⟨earlier, heariler, hkeyEarlier⟩ := hiAfter
  obtain ⟨later, hlater⟩ := source.read_eq_some hvalid hj
  have hlaterEarlierFalse :=
    hsorted i j (by omega) hj hij earlier later heariler hlater
  have hlaterEarlier : ¬lt later.key earlier.key = true := by
    simp [hlaterEarlierFalse]
  by_cases hkeyLater : lt key later.key = true
  · exact ⟨later, hlater, hkeyLater⟩
  · by_cases hearilerLater : lt earlier.key later.key = true
    · exact False.elim (hkeyLater
      (horder.trans key earlier.key later.key hkeyEarlier hearilerLater))
    · by_cases hlaterKey : lt later.key key = true
      · exact False.elim (hlaterEarlier
        (horder.trans later.key key earlier.key hlaterKey hkeyEarlier))
      · have hearilerLaterIncomp :
        ¬lt earlier.key later.key = true ∧
          ¬lt later.key earlier.key = true :=
        ⟨hearilerLater, hlaterEarlier⟩
        have hlaterKeyIncomp :
          ¬lt later.key key = true ∧ ¬lt key later.key = true :=
          ⟨hlaterKey, hkeyLater⟩
        have hearilerKeyIncomp := horder.incomp_trans earlier.key later.key key
          hearilerLaterIncomp hlaterKeyIncomp
        exact False.elim (hearilerKeyIncomp.2 hkeyEarlier)

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[gallopDualBefore_prefix_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma gallopDualBefore_prefix_of_sorted
  (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ) (n : Nat)
  (hvalid : source.ValidRange n) (horder : BoolStrictWeakOrder lt)
  (hsorted : GallopSortedRange lt source n) :
  GallopPrefix (GallopBefore (gallopComparatorDual lt) source key) n := by
  have hsuffix := gallopAfter_suffix_of_sorted lt source key n hvalid horder hsorted
  intro i j hij hj hjBefore
  obtain ⟨later, hlater, hdualLater⟩ := hjBefore
  have hlaterNotAfter : ¬GallopAfter lt source key j :=
    read_not_after_of_dual_true lt source key hlater hdualLater
  obtain ⟨earlier, heariler⟩ := source.read_eq_some hvalid (by omega : i < n)
  by_cases hafter : lt key earlier.key = true
  · exact False.elim (hlaterNotAfter
    (hsuffix i j hij hj ⟨earlier, heariler, hafter⟩))
  · refine ⟨earlier, heariler, ?_⟩
    have hfalse : lt key earlier.key = false :=
      Bool.eq_false_of_not_eq_true hafter
    simp [gallopComparatorDual, hfalse]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[leftPartition_to_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma leftPartition_to_slice
  (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (slice : SortSlice κ ν) (base : Int) (key : κ) (n k : Nat)
  (hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice base n)
  (hpartition : GallopPartition (GallopBefore lt source key) n k) :
  GallopLeftPartition lt slice base key n k := by
  obtain ⟨hk, hbefore, hafter⟩ := hpartition
  refine ⟨hk, ?_, ?_⟩
  · intro i hi
    obtain ⟨entry, hread, hcompare⟩ := hbefore i hi
    have hin : i < n := by omega
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩
  · intro i hki hin
    obtain ⟨entry, hread⟩ := source.read_eq_some hvalid hin
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    have hnot := hafter i hki hin
    have hcompare : lt entry.key key = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hnot ⟨entry, hread, htrue⟩
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[dualPartition_to_right_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
private lemma dualPartition_to_right_slice
  (lt : BoolComparator κ) (source : GallopKeySource κ ν)
  (slice : SortSlice κ ν) (base : Int) (key : κ) (n k : Nat)
  (hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice base n)
  (hpartition : GallopPartition
    (GallopBefore (gallopComparatorDual lt) source key) n k) :
  GallopRightPartition lt slice base key n k := by
  obtain ⟨hk, hbefore, hafter⟩ := hpartition
  refine ⟨hk, ?_, ?_⟩
  · intro i hi
    obtain ⟨entry, hread, hdual⟩ := hbefore i hi
    have hin : i < n := by omega
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    have hcompare : lt key entry.key = false := by
      simpa [gallopComparatorDual] using hdual
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩
  · intro i hki hin
    obtain ⟨entry, hread⟩ := source.read_eq_some hvalid hin
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    have hnot := hafter i hki hin
    have hcompare : lt key entry.key = true := by
      by_contra hfalse
      have hrawFalse : lt key entry.key = false :=
        Bool.eq_false_of_not_eq_true hfalse
      apply hnot
      refine ⟨entry, hread, ?_⟩
      simp [gallopComparatorDual, hrawFalse]
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeft_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopLeft_correct
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice base n)
  (horder : BoolStrictWeakOrder state.key_compare)
  (hsorted : GallopSortedRange state.key_compare source n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, gallopLeft? state slice base key n hint = some result ∧ result.fuelExhausted = false ∧ GallopLeftPartition state.key_compare slice base key n result.index := by
-- proof
  have hprefix := gallopBefore_prefix_of_sorted state.key_compare source key n
    hvalid horder hsorted
  rcases gallopLeftFromSource_partition state source key n hint hvalid hprefix
    hn hhint hnmax with ⟨result, hresult, hfuel, hpartition⟩
  refine ⟨result, ?_, hfuel,
    leftPartition_to_slice state.key_compare source slice base key n
      result.index hvalid hagrees hpartition⟩
  rw [← gallopLeftFromSource_eq_slice state source slice base key n hint
    hvalid hagrees hn hhint hnmax]
  exact hresult

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_correct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopRight_correct
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hagrees : source.AgreesWithSlice slice base n)
  (horder : BoolStrictWeakOrder state.key_compare)
  (hsorted : GallopSortedRange state.key_compare source n)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, gallopRight? state slice base key n hint = some result ∧ result.fuelExhausted = false ∧ GallopRightPartition state.key_compare slice base key n result.index := by
-- proof
  have hprefix := gallopDualBefore_prefix_of_sorted state.key_compare source key
    n hvalid horder hsorted
  rcases gallopLeftFromSource_partition (gallopDualState state) source key n hint
    hvalid (by simpa using hprefix) hn hhint hnmax with
    ⟨result, hleftResult, hfuel, hpartition⟩
  have hsourceDual :
    gallopRightFromSource? state source key n hint =
      gallopLeftFromSource? (gallopDualState state) source key n hint := by
    have htrace := congrArg TraceResult.erase
      (gallopRight_eq_left_dual state source key n hint)
    simpa using htrace
  have hrightResult :
    gallopRightFromSource? state source key n hint = some result := by
    rwa [hsourceDual]
  refine ⟨result, ?_, hfuel,
    dualPartition_to_right_slice state.key_compare source slice base key n
      result.index hvalid hagrees (by simpa using hpartition)⟩
  rw [← gallopRightFromSource_eq_slice state source slice base key n hint
    hvalid hagrees hn hhint hnmax]
  exact hrightResult

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeft_correct_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopLeft_correct_of_sorted
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
  {keys : Array κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hslice : source.AgreesWithSlice slice base n)
  (hkeys : GallopKeyArrayAgreement source n keys)
  (horder : BoolStrictWeakOrder state.key_compare)
  (hsorted : Sorted state.key_compare keys)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, gallopLeft? state slice base key n hint = some result ∧ result.fuelExhausted = false ∧ GallopLeftPartition state.key_compare slice base key n result.index := by
-- proof
  exact gallopLeft_correct state source slice base key n hint hvalid hslice
    horder (gallopSortedRange_of_sorted state.key_compare source n keys hkeys
      hsorted) hn hhint hnmax

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_correct_of_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopRight_correct_of_sorted
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {source : GallopKeySource κ ν}
  {slice : SortSlice κ ν}
  {base : Int}
  {key : κ}
  {keys : Array κ}
-- given
  (n hint : Nat)
  (hvalid : source.ValidRange n)
  (hslice : source.AgreesWithSlice slice base n)
  (hkeys : GallopKeyArrayAgreement source n keys)
  (horder : BoolStrictWeakOrder state.key_compare)
  (hsorted : Sorted state.key_compare keys)
  (hn : 0 < n)
  (hhint : hint < n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  ∃ result, gallopRight? state slice base key n hint = some result ∧ result.fuelExhausted = false ∧ GallopRightPartition state.key_compare slice base key n result.index := by
-- proof
  exact gallopRight_correct state source slice base key n hint hvalid hslice
    horder (gallopSortedRange_of_sorted state.key_compare source n keys hkeys
      hsorted) hn hhint hnmax

end CPythonListsort

namespace CPythonListsort

/--
[gallopLeft_duplicate_boundary_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopLeft_duplicate_boundary_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  gallopLeft? gallopDuplicateRegressionState gallopDuplicateRegressionSlice 0 2 4 2 = some { index := 1, fuelExhausted := false } := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[gallopRight_duplicate_boundary_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean)
-/
@[path]
lemma gallopRight_duplicate_boundary_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  gallopRight? gallopDuplicateRegressionState gallopDuplicateRegressionSlice 0 2 4 2 = some { index := 3, fuelExhausted := false } := by
-- proof
  decide

end CPythonListsort


-- created on 2026-10-23
