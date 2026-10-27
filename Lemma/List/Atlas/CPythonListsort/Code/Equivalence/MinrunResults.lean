import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.CPythonListsort.Code.Equivalence.MinrunResults.Part3
open CPythonListsort


namespace CPythonListsort

/--
[minrunExponentSpecLoop_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunExponentSpecLoop_characterization
  {fuel listSize exponent : Nat}
-- given
  (hwitness : ∃ d < fuel, listSize / 2 ^ (exponent + d) < 64) :
-- imply
  let out := minrunExponentSpecLoop fuel listSize exponent out.2 = true ∧ out.1 < exponent + fuel ∧ listSize / 2 ^ out.1 < 64 ∧ ∀ j, exponent ≤ j → j < out.1 → 64 ≤ listSize / 2 ^ j := by
-- proof
  induction fuel generalizing exponent with
  | zero =>
    obtain ⟨d, hd, _⟩ := hwitness
    omega
  | succ fuel ih =>
    simp only [minrunExponentSpecLoop]
    by_cases hcurrent : listSize >>> exponent < 64
    · rw [if_pos hcurrent]
      constructor
      · rfl
      constructor
      · omega
      constructor
      · simpa [Nat.shiftRight_eq_div_pow] using hcurrent
      · intro j _ hj
        omega
    · rw [if_neg hcurrent]
      have hcurrentDiv : 64 ≤ listSize / 2 ^ exponent := by
        rw [Nat.shiftRight_eq_div_pow] at hcurrent
        omega
      obtain ⟨d, hdFuel, hd⟩ := hwitness
      have hdPos : 0 < d := by
        by_contra hnot
        have hdZero : d = 0 := by omega
        subst d
        simp only [Nat.add_zero] at hd
        omega
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
      have htailWitness : ∃ d' < fuel,
        listSize / 2 ^ (exponent + 1 + d') < 64 := by
        refine ⟨d, by omega, ?_⟩
        have heq : exponent + d.succ = exponent + 1 + d := by omega
        rwa [heq] at hd
      have htail := ih (exponent + 1) htailWitness
      obtain ⟨hstopped, hbound, hsuccess, hleast⟩ := htail
      refine ⟨hstopped, ?_, hsuccess, ?_⟩
      · omega
      · intro j hjLower hjUpper
        by_cases hj : j = exponent
        · subst j
          exact hcurrentDiv
        · exact hleast j (by omega) hjUpper

end CPythonListsort

namespace CPythonListsort

/--
[minrunExponentCharacterization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunExponentCharacterization
  {listSize : PySSize}
-- given
  (_hlistSize : listSize.Nonnegative)
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  let out := minrunExponentSpecLoop 64 listSize.toNat 0 out.2 = true ∧ out.1 < 64 ∧ listSize.toNat / 2 ^ out.1 < 64 ∧ ∀ j < out.1, 64 ≤ listSize.toNat / 2 ^ j := by
-- proof
  have hwitness : ∃ d < 64, listSize.toNat / 2 ^ (0 + d) < 64 := by
    refine ⟨63, by omega, ?_⟩
    have hlt : listSize.toNat < 2 ^ 63 := by
      rw [pyListMax_eq] at hmax
      norm_num at hmax ⊢
      omega
    rw [Nat.zero_add, Nat.div_eq_of_lt hlt]
    omega
  have hspec := minrunExponentSpecLoop_characterization 64 listSize.toNat 0 hwitness
  simpa using hspec

end CPythonListsort

namespace CPythonListsort

/--
[minrunExponent_lt_64](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunExponent_lt_64
  {listSize : PySSize}
-- given
  (hlistSize : listSize.Nonnegative)
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 64 :=
-- proof
  (minrunExponentCharacterization listSize hlistSize hmax).2.1

end CPythonListsort

namespace CPythonListsort

/--
[minrunInit_stops_and_exponent_lt_64](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunInit_stops_and_exponent_lt_64
  {listSize : PySSize}
-- given
  (hlistSize : listSize.Nonnegative)
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  (minrunInitTraced listSize).stopped = true ∧ (minrunInit listSize).mr_e.toNat < 64 := by
-- proof
  have hinit := minrunInit_exponent_eq_spec listSize hlistSize
  have hcharacterization := minrunExponentCharacterization listSize hlistSize hmax
  dsimp only at hinit hcharacterization ⊢
  exact ⟨hinit.2.2.trans hcharacterization.1, hinit.1.trans_lt hcharacterization.2.1⟩

end CPythonListsort

namespace CPythonListsort

/--
[minrunExponent_le_60](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunExponent_le_60
  {listSize : PySSize}
-- given
  (hlistSize : listSize.Nonnegative)
  (hmax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  (minrunExponentSpecLoop 64 listSize.toNat 0).1 ≤ 60 := by
-- proof
  have hcharacterization := minrunExponentCharacterization listSize hlistSize hmax
  dsimp only at hcharacterization
  by_contra hnot
  have hleast := hcharacterization.2.2.2 60 (by omega)
  have hlt : listSize.toNat < 2 ^ 60 := by
    rw [pyListMax_eq] at hmax
    norm_num at hmax ⊢
    omega
  rw [Nat.div_eq_of_lt hlt] at hleast
  omega

end CPythonListsort

namespace CPythonListsort

/--
[minrunInit_modulus_le_listSize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunInit_modulus_le_listSize
  {listSize : PySSize}
-- given
  (hNonnegative : listSize.Nonnegative)
  (hMax : listSize.toNat ≤ PY_LIST_MAX)
  (hPositive : 0 < listSize.toNat) :
-- imply
  2 ^ (minrunInit listSize).mr_e.toNat ≤ listSize.toNat := by
-- proof
  let out := minrunExponentSpecLoop 64 listSize.toNat 0
  have hinit := minrunInit_exponent_eq_spec listSize hNonnegative
  have hcharacterization :=
    minrunExponentCharacterization listSize hNonnegative hMax
  change 2 ^ (minrunInit listSize).mr_e.toNat ≤ listSize.toNat
  rw [hinit.1]
  by_cases hzero : out.1 = 0
  · rw [hzero]
    exact hPositive
  · obtain ⟨exponent, hexponent⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    change 2 ^ out.1 ≤ listSize.toNat
    dsimp only at hcharacterization
    rw [hexponent] at hcharacterization ⊢
    have hprevious :
      64 ≤ listSize.toNat / 2 ^ exponent := by
      exact hcharacterization.2.2.2 exponent (by omega)
    have hpowPositive : 0 < 2 ^ exponent := by positivity
    have hscaled : 64 * 2 ^ exponent ≤ listSize.toNat :=
      (Nat.le_div_iff_mul_le hpowPositive).mp hprevious
    rw [pow_succ]
    omega

end CPythonListsort

namespace CPythonListsort

/--
[minrunInit_mask_lt_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunInit_mask_lt_modulus
  {listSize : PySSize}
-- given
  (hNonnegative : listSize.Nonnegative)
  (hMax : listSize.toNat ≤ PY_LIST_MAX) :
-- imply
  (minrunInit listSize).mr_mask.toNat < 2 ^ (minrunInit listSize).mr_e.toNat := by
-- proof
  simp only [minrunInit, minrunInitTraced]
  rw [minrunExponentLoop_eq_spec 64 listSize 0 hNonnegative]
  have hbound := minrunExponent_lt_64 listSize hNonnegative hMax
  have hlt : (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 2 ^ 64 := by
    norm_num at hbound ⊢
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact cIntMinrunMask_toNat_lt_pow _

end CPythonListsort

namespace CPythonListsort

/--
[minrunInit_rangeInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
private lemma minrunInit_rangeInv
  (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
  (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat) :
  MinrunRangeInv (minrunInit listSize) := by
  have hinit := minrunInit_exponent_eq_spec listSize hNonnegative
  have hcharacterization :=
    minrunExponentCharacterization listSize hNonnegative hMax
  constructor
  · simpa [minrunInit, minrunInitTraced] using hMax
  · rw [hinit.1]
    exact minrunExponent_le_60 listSize hNonnegative hMax
  · rw [hinit.2.1]
    simp
  · exact minrunInit_mask_lt_modulus listSize hNonnegative hMax
  · exact minrunInit_modulus_le_listSize listSize hNonnegative hMax hPositive
  · rw [hinit.1]
    exact hcharacterization.2.2.1

end CPythonListsort

namespace CPythonListsort

/--
[minrun_cIntMask_truncation_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrun_cIntMask_truncation_regression
-- imply
  let listSize : PySSize := BitVec.ofNat 64 (2 ^ 39 - 2 ^ 32) (minrunInit listSize).mr_e.toNat = 33 ∧ (minrunInit listSize).mr_mask.toNat = 2 ^ 32 - 1 ∧ (minrunNextN 2 (minrunInit listSize)).outputs = [63, 63] ∧ (minrunSpecTrace 2 listSize.toNat 33 0).outputs = [63, 64] := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[minrunSpecTrace_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunSpecTrace_prefix
  {calls listlen exponent current : Nat}
-- given
  (hcurrent : current < 2 ^ exponent) :
-- imply
  let trace := minrunSpecTrace calls listlen exponent current trace.outputs.sum = (current + calls * listlen) / 2 ^ exponent ∧ trace.residual = (current + calls * listlen) % 2 ^ exponent ∧ trace.residual < 2 ^ exponent := by
-- proof
  induction calls generalizing current with
  | zero =>
    have hpow : 0 < 2 ^ exponent := pow_pos (by omega) _
    simp [minrunSpecTrace, Nat.div_eq_of_lt hcurrent,
      Nat.mod_eq_of_lt hcurrent, hcurrent]
  | succ calls ih =>
    let modulus := 2 ^ exponent
    let total := current + listlen
    let quotient := total / modulus
    let residual := total % modulus
    have hmodulus : 0 < modulus := by
      simp [modulus]
    have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
    have htail := ih residual hresidual
    change
      quotient + (minrunSpecTrace calls listlen exponent residual).outputs.sum =
        (current + (calls + 1) * listlen) / modulus ∧
        (minrunSpecTrace calls listlen exponent residual).residual =
          (current + (calls + 1) * listlen) % modulus ∧
        (minrunSpecTrace calls listlen exponent residual).residual < modulus
    obtain ⟨htailSum, htailResidual, htailBound⟩ := htail
    rw [htailSum, htailResidual]
    have hdecompose : residual + modulus * quotient = total := by
      exact Nat.mod_add_div total modulus
    have htotalEq : modulus * quotient + (residual + calls * listlen) =
      current + (calls + 1) * listlen := by
      calc
        modulus * quotient + (residual + calls * listlen) =
          (residual + modulus * quotient) + calls * listlen := by ring
        _ = total + calls * listlen := by rw [hdecompose]
        _ = current + (calls + 1) * listlen := by
          simp only [total]
          ring
    constructor
    · calc
      quotient + (residual + calls * listlen) / modulus =
        (modulus * quotient + (residual + calls * listlen)) / modulus := by
          rw [Nat.mul_add_div hmodulus]
      _ = (current + (calls + 1) * listlen) / modulus := by rw [htotalEq]
    constructor
    · calc
      (residual + calls * listlen) % modulus =
        (modulus * quotient + (residual + calls * listlen)) % modulus := by
          rw [Nat.mul_add_mod_self_left]
      _ = (current + (calls + 1) * listlen) % modulus := by rw [htotalEq]
    · exact Nat.mod_lt _ hmodulus

end CPythonListsort

namespace CPythonListsort

/--
[minrunPrefixSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunPrefixSum
  {listSize : PySSize}
  {calls : Nat}
-- given
  (hlistSize : listSize.Nonnegative)
  (hmax : listSize.toNat ≤ PY_LIST_MAX)
  (hexponent32 : (minrunInit listSize).mr_e.toNat < 32)
  (_hcalls : calls ≤ 2 ^ (minrunInit listSize).mr_e.toNat) :
-- imply
  let state := minrunInit listSize let run := minrunNextN calls state let modulus := 2 ^ state.mr_e.toNat run.outputs.sum = (calls * listSize.toNat) / modulus ∧ run.state.mr_current.toNat = (calls * listSize.toNat) % modulus ∧ run.state.mr_current.toNat < modulus ∧ run.state.mr_current.toNat + listSize.toNat < 2 ^ 63 ∧ run.assertionsPassed = true := by
-- proof
  let state := minrunInit listSize
  let exponentResult := minrunExponentSpecLoop 64 listSize.toNat 0
  have hinitExponent := minrunInit_exponent_eq_spec listSize hlistSize
  have hspecified32 : exponentResult.1 < 32 := by
    rwa [← hinitExponent.1]
  have hinit := minrunInit_eq_spec listSize hlistSize hspecified32
  change state.mr_e.toNat = exponentResult.1 ∧
    state.mr_mask = ((1 : PySSize) <<< exponentResult.1) - 1 ∧
    state.mr_current = 0 ∧ (minrunInitTraced listSize).stopped = exponentResult.2 at hinit
  have hexponent : state.mr_e.toNat < 32 := by
    exact hexponent32
  have hexponent60 : state.mr_e.toNat ≤ 60 := by
    rw [hinit.1]
    exact minrunExponent_le_60 listSize hlistSize hmax
  have hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1 := by
    rwa [hinit.1]
  have hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    rw [hinit.2.2.1]
    simp
  have hstateList : state.listlen.toNat = listSize.toNat := by
    simp [state, minrunInit, minrunInitTraced]
  have hrun := minrunNextN_eq_spec calls state hexponent hexponent60 hmask hcurrent
    (by rwa [hstateList])
  have hpure := minrunSpecTrace_prefix calls state.listlen.toNat
    state.mr_e.toNat state.mr_current.toNat hcurrent
  change
    (minrunNextN calls state).outputs.sum =
      (calls * listSize.toNat) / 2 ^ state.mr_e.toNat ∧
      (minrunNextN calls state).state.mr_current.toNat =
        (calls * listSize.toNat) % 2 ^ state.mr_e.toNat ∧
      (minrunNextN calls state).state.mr_current.toNat < 2 ^ state.mr_e.toNat ∧
      (minrunNextN calls state).state.mr_current.toNat + listSize.toNat < 2 ^ 63 ∧
      (minrunNextN calls state).assertionsPassed = true
  dsimp only at hrun hpure
  obtain ⟨houtputs, hresidual, hassertions⟩ := hrun
  obtain ⟨hsum, hpureResidual, hresidualBound⟩ := hpure
  have hcurrentNat : state.mr_current.toNat = 0 := by
    rw [hinit.2.2.1]
    rfl
  have hsumFinal : (minrunNextN calls state).outputs.sum =
    (calls * listSize.toNat) / 2 ^ state.mr_e.toNat := by
    calc
      (minrunNextN calls state).outputs.sum =
        (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
          state.mr_current.toNat).outputs.sum := congrArg List.sum houtputs
      _ = (state.mr_current.toNat + calls * state.listlen.toNat) /
        2 ^ state.mr_e.toNat := hsum
      _ = (calls * listSize.toNat) / 2 ^ state.mr_e.toNat := by
        rw [hcurrentNat, hstateList, Nat.zero_add]
  have hresidualFinal : (minrunNextN calls state).state.mr_current.toNat =
    (calls * listSize.toNat) % 2 ^ state.mr_e.toNat := by
    calc
      (minrunNextN calls state).state.mr_current.toNat =
        (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
          state.mr_current.toNat).residual := hresidual
      _ = (state.mr_current.toNat + calls * state.listlen.toNat) %
        2 ^ state.mr_e.toNat := hpureResidual
      _ = (calls * listSize.toNat) % 2 ^ state.mr_e.toNat := by
        rw [hcurrentNat, hstateList, Nat.zero_add]
  have hresidualFinalBound :
    (minrunNextN calls state).state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    rw [hresidualFinal]
    exact Nat.mod_lt _ (pow_pos (by omega) _)
  have hpowLe : 2 ^ state.mr_e.toNat ≤ 2 ^ 60 :=
    Nat.pow_le_pow_right (by omega) hexponent60
  have haddition :
    (minrunNextN calls state).state.mr_current.toNat + listSize.toNat < 2 ^ 63 := by
    rw [pyListMax_eq] at hmax
    norm_num at hpowLe hmax
    omega
  exact ⟨hsumFinal, hresidualFinal, hresidualFinalBound, haddition, hassertions⟩

end CPythonListsort

namespace CPythonListsort

/--
[minrunCeilDiv_eq_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
private lemma minrunCeilDiv_eq_succ (x modulus : Nat)
  (hmodulus : 0 < modulus)
  (hremainder : 0 < x % modulus) :
  minrunCeilDiv x modulus = x / modulus + 1 := by
  let quotient := x / modulus
  let residual := x % modulus
  have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
  have hdecompose : modulus * quotient + residual = x := Nat.div_add_mod x modulus
  have htailDiv : (residual + modulus - 1) / modulus = 1 := by
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  unfold minrunCeilDiv
  have htotal : x + modulus - 1 = modulus * quotient + (residual + modulus - 1) := by
    omega
  rw [htotal, Nat.mul_add_div hmodulus, htailDiv]

end CPythonListsort

namespace CPythonListsort

/--
[minrunSpecTrace_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunSpecTrace_length
  {calls listlen exponent current : Nat} :
-- imply
  (minrunSpecTrace calls listlen exponent current).outputs.length = calls := by
-- proof
  induction calls generalizing current with
  | zero => simp [minrunSpecTrace]
  | succ calls ih => simp [minrunSpecTrace, ih]

end CPythonListsort

namespace CPythonListsort

/--
[minrunSequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
lemma minrunSequence
  {listSize : PySSize}
-- given
  (hlistSize : listSize.Nonnegative)
  (hmax : listSize.toNat ≤ PY_LIST_MAX)
  (hexponent32 : (minrunInit listSize).mr_e.toNat < 32) :
-- imply
  let state := minrunInit listSize let modulus := 2 ^ state.mr_e.toNat let run := minrunNextN modulus state run.outputs.length = modulus ∧ (∀ x ∈ run.outputs, x = listSize.toNat / modulus ∨ x = minrunCeilDiv listSize.toNat modulus) ∧ run.outputs.sum = listSize.toNat ∧ run.state.mr_current.toNat = 0 ∧ run.assertionsPassed = true := by
-- proof
  let state := minrunInit listSize
  let modulus := 2 ^ state.mr_e.toNat
  let run := minrunNextN modulus state
  have hpref := minrunPrefixSum listSize hlistSize hmax hexponent32 modulus (by rfl)
  change
    run.outputs.sum = (modulus * listSize.toNat) / modulus ∧
      run.state.mr_current.toNat = (modulus * listSize.toNat) % modulus ∧
      run.state.mr_current.toNat < modulus ∧
      run.state.mr_current.toNat + listSize.toNat < 2 ^ 63 ∧
      run.assertionsPassed = true at hpref
  let exponentResult := minrunExponentSpecLoop 64 listSize.toNat 0
  have hinitExponent := minrunInit_exponent_eq_spec listSize hlistSize
  have hspecified32 : exponentResult.1 < 32 := by
    rwa [← hinitExponent.1]
  have hinit := minrunInit_eq_spec listSize hlistSize hspecified32
  change state.mr_e.toNat = exponentResult.1 ∧
    state.mr_mask = ((1 : PySSize) <<< exponentResult.1) - 1 ∧
    state.mr_current = 0 ∧ (minrunInitTraced listSize).stopped = exponentResult.2 at hinit
  have hexponent : state.mr_e.toNat < 32 := by
    exact hexponent32
  have hexponent60 : state.mr_e.toNat ≤ 60 := by
    rw [hinit.1]
    exact minrunExponent_le_60 listSize hlistSize hmax
  have hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1 := by
    rwa [hinit.1]
  have hcurrentNat : state.mr_current.toNat = 0 := by
    rw [hinit.2.2.1]
    rfl
  have hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    rw [hcurrentNat]
    simp
  have hstateList : state.listlen.toNat = listSize.toNat := by
    simp [state, minrunInit, minrunInitTraced]
  have hrun := minrunNextN_eq_spec modulus state hexponent hexponent60 hmask hcurrent
    (by rwa [hstateList])
  dsimp only at hrun
  obtain ⟨houtputs, _, _⟩ := hrun
  have hlength : run.outputs.length = modulus := by
    change (minrunNextN modulus state).outputs.length = modulus
    rw [houtputs, minrunSpecTrace_length]
  have hbalancedSpec := minrunSpecTrace_balanced modulus state.listlen.toNat
    state.mr_e.toNat state.mr_current.toNat hcurrent (by
      intro _
      exact hcurrentNat)
  have hbalanced : ∀ x ∈ run.outputs,
    x = listSize.toNat / modulus ∨ x = minrunCeilDiv listSize.toNat modulus := by
    intro x hx
    have hxSpec : x ∈ (minrunSpecTrace modulus state.listlen.toNat state.mr_e.toNat
      state.mr_current.toNat).outputs := by
      rwa [← houtputs]
    have hxBalanced := hbalancedSpec x hxSpec
    simpa [modulus, hstateList] using hxBalanced
  have hmodulus : 0 < modulus := by simp [modulus]
  have hsum : run.outputs.sum = listSize.toNat := by
    calc
      run.outputs.sum = (modulus * listSize.toNat) / modulus := hpref.1
      _ = listSize.toNat := Nat.mul_div_right _ hmodulus
  have hresidual : run.state.mr_current.toNat = 0 := by
    calc
      run.state.mr_current.toNat = (modulus * listSize.toNat) % modulus := hpref.2.1
      _ = 0 := by simp
  exact ⟨hlength, hbalanced, hsum, hresidual, hpref.2.2.2.2⟩

end CPythonListsort

/--
[minrunNextN_output_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
private lemma minrunNextN_output_bounds_eq
  {listSize : PySSize}
  {calls : Nat}
-- given
  (hNonnegative : listSize.Nonnegative)
  (hMax : listSize.toNat ≤ PY_LIST_MAX)
  (hPositive : 0 < listSize.toNat) :
-- imply
  let run := minrunNextN calls (minrunInit listSize) run.assertionsPassed = true ∧ ∀ target ∈ run.outputs, 1 ≤ target ∧ target ≤ MAX_MINRUN.toNat := by
-- proof
  apply CPythonListsort.minrunNextN_output_bounds listSize hNonnegative hMax hPositive calls

/--
[minrunNext_after_init_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
private lemma minrunNext_after_init_bounds_eq
  {listSize : PySSize}
  {calls : Nat}
-- given
  (hNonnegative : listSize.Nonnegative)
  (hMax : listSize.toNat ≤ PY_LIST_MAX)
  (hPositive : 0 < listSize.toNat) :
-- imply
  let state := (minrunNextN calls (minrunInit listSize)).state (minrunNext state).assertionPassed = true ∧ 1 ≤ (minrunNext state).result.toNat ∧ (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat := by
-- proof
  apply CPythonListsort.minrunNext_after_init_bounds listSize hNonnegative hMax hPositive calls

/--
[minrunNextN_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
private lemma minrunNextN_eq_spec_eq
  {calls : Nat}
  {state : MinrunState}
-- given
  (hexponent : state.mr_e.toNat < 32)
  (hexponent60 : state.mr_e.toNat ≤ 60)
  (hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1)
  (hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat)
  (hlistMax : state.listlen.toNat ≤ PY_LIST_MAX) :
-- imply
  let trace := minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat state.mr_current.toNat (minrunNextN calls state).outputs = trace.outputs ∧ (minrunNextN calls state).state.mr_current.toNat = trace.residual ∧ (minrunNextN calls state).assertionsPassed = true := by
-- proof
  apply CPythonListsort.minrunNextN_eq_spec calls state hexponent hexponent60 hmask hcurrent hlistMax

/--
[minrunSpecTrace_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean)
-/
@[path]
private lemma minrunSpecTrace_balanced_eq
  {calls listlen exponent current : Nat}
-- given
  (hcurrent : current < 2 ^ exponent)
  (hzero : listlen % 2 ^ exponent = 0 → current = 0) :
-- imply
  ∀ x ∈ (minrunSpecTrace calls listlen exponent current).outputs, x = listlen / 2 ^ exponent ∨ x = minrunCeilDiv listlen (2 ^ exponent) := by
-- proof
  apply CPythonListsort.minrunSpecTrace_balanced calls listlen exponent current hcurrent hzero


-- created on 2026-10-23
