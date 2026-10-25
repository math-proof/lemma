import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
open CPythonListsort


namespace CPythonListsort

/--
[maxMinrun_msb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
private lemma maxMinrun_msb : MAX_MINRUN.msb = false := by
decide

end CPythonListsort

namespace CPythonListsort

/--
[maxMinrun_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
private lemma maxMinrun_toNat : MAX_MINRUN.toNat = 64 := by
decide

end CPythonListsort

namespace CPythonListsort

/--
[shifted_slt_maxMinrun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
private lemma shifted_slt_maxMinrun (x : PySSize) (exponent : Nat)
  (hx : x.Nonnegative) :
  (x.sshiftRight exponent).slt MAX_MINRUN = decide (x.toNat >>> exponent < 64) := by
  have hshift : (x.sshiftRight exponent).msb = false := by
    simpa [PySSize.Nonnegative] using hx
  rw [BitVec.slt_eq_decide]
  rw [BitVec.toInt_eq_toNat_of_msb hshift]
  rw [BitVec.toInt_eq_toNat_of_msb maxMinrun_msb]
  rw [BitVec.toNat_sshiftRight_of_msb_false hx]
  simp only [maxMinrun_toNat]
  norm_cast

end CPythonListsort

namespace CPythonListsort

/--
[minrunExponentLoop_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
lemma minrunExponentLoop_eq_spec
  {fuel : Nat}
  {listSize : PySSize}
  {exponent : Nat}
-- given
  (hlistSize : listSize.Nonnegative) :
-- imply
  minrunExponentLoop fuel listSize exponent = minrunExponentSpecLoop fuel listSize.toNat exponent := by
-- proof
  induction fuel generalizing exponent with
  | zero => rfl
  | succ fuel ih =>
    simp only [minrunExponentLoop, minrunExponentSpecLoop]
    rw [shifted_slt_maxMinrun listSize exponent hlistSize]
    split <;> simp_all

end CPythonListsort

namespace CPythonListsort

/--
[minrunExponentSpecLoop_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
private lemma minrunExponentSpecLoop_le (fuel listSize exponent : Nat) :
  (minrunExponentSpecLoop fuel listSize exponent).1 ≤ exponent + fuel := by
  induction fuel generalizing exponent with
  | zero => simp [minrunExponentSpecLoop]
  | succ fuel ih =>
    simp only [minrunExponentSpecLoop]
    split
    · omega
    · have := ih (exponent + 1)
      omega

end CPythonListsort

namespace CPythonListsort

/--
[one_shift32_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
has its mathematical power-of-two value. -/
private lemma one_shift32_toNat {exponent : Nat} (hexponent : exponent < 32) :
  (((1 : BitVec 32) <<< exponent).toNat) = 2 ^ exponent := by
  have hpow : 2 ^ exponent < 2 ^ 32 :=
    Nat.pow_lt_pow_right (a := 2) (by omega) hexponent
  have hone : (1 : BitVec 32).toNat = 1 := by decide
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [hone, one_mul, Nat.mod_eq_of_lt hpow]

end CPythonListsort

namespace CPythonListsort

/--
[one_shift_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
private lemma one_shift_toNat {exponent : Nat} (hexponent : exponent < 64) :
  (((1 : PySSize) <<< exponent).toNat) = 2 ^ exponent := by
  have hpow : 2 ^ exponent < 2 ^ 64 :=
    Nat.pow_lt_pow_right (a := 2) (by omega) hexponent
  have hone : (1 : PySSize).toNat = 1 := by decide
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [hone, one_mul, Nat.mod_eq_of_lt hpow]

end CPythonListsort

namespace CPythonListsort

/--
[cIntMask_eq_fullMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
the mathematical `Py_ssize_t` mask used by the quotient/remainder specification. -/
private lemma cIntMask_eq_fullMask {exponent : Nat}
  (hexponent : exponent < 32) :
  ((((1 : BitVec 32) <<< exponent) - 1).zeroExtend 64) =
    ((1 : PySSize) <<< exponent) - 1 := by
  have hone32 : (1 : BitVec 32).toNat = 1 := by decide
  have hone64 : (1 : PySSize).toNat = 1 := by decide
  have honeLe32 : (1 : BitVec 32) ≤ (1 : BitVec 32) <<< exponent := by
    rw [BitVec.le_def, one_shift32_toNat hexponent]
    simpa using Nat.one_le_two_pow
  have honeLe64 : (1 : PySSize) ≤ (1 : PySSize) <<< exponent := by
    rw [BitVec.le_def, one_shift_toNat (by omega)]
    simpa using Nat.one_le_two_pow
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le (by omega),
    BitVec.toNat_sub_of_le honeLe32,
    BitVec.toNat_sub_of_le honeLe64,
    one_shift32_toNat hexponent,
    one_shift_toNat (by omega), hone32, hone64]

end CPythonListsort

namespace CPythonListsort

/--
[minrunInit_exponent_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
lemma minrunInit_exponent_eq_spec
  {listSize : PySSize}
-- given
  (hlistSize : listSize.Nonnegative) :
-- imply
  let specified := minrunExponentSpecLoop 64 listSize.toNat 0 (minrunInit listSize).mr_e.toNat = specified.1 ∧ (minrunInit listSize).mr_current = 0 ∧ (minrunInitTraced listSize).stopped = specified.2 := by
-- proof
  simp only [minrunInit, minrunInitTraced]
  rw [minrunExponentLoop_eq_spec 64 listSize 0 hlistSize]
  have hbound := minrunExponentSpecLoop_le 64 listSize.toNat 0
  have hlt : (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 2 ^ 64 := by
    norm_num at hbound ⊢
    omega
  constructor
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  simp

end CPythonListsort

namespace CPythonListsort

/--
[minrunInit_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
lemma minrunInit_eq_spec
  {listSize : PySSize}
-- given
  (hlistSize : listSize.Nonnegative)
  (hexponent : (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 32) :
-- imply
  let specified := minrunExponentSpecLoop 64 listSize.toNat 0 (minrunInit listSize).mr_e.toNat = specified.1 ∧ (minrunInit listSize).mr_mask = ((1 : PySSize) <<< specified.1) - 1 ∧ (minrunInit listSize).mr_current = 0 ∧ (minrunInitTraced listSize).stopped = specified.2 := by
-- proof
  simp only [minrunInit, minrunInitTraced]
  rw [minrunExponentLoop_eq_spec 64 listSize 0 hlistSize]
  have hbound := minrunExponentSpecLoop_le 64 listSize.toNat 0
  have hlt : (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 2 ^ 64 := by
    norm_num at hbound ⊢
    omega
  constructor
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  constructor
  · exact cIntMask_eq_fullMask hexponent
  simp

end CPythonListsort

namespace CPythonListsort

/--
[mask_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
private lemma mask_toNat {exponent : Nat} (hexponent : exponent < 32) :
  ((((1 : PySSize) <<< exponent) - 1).toNat) = 2 ^ exponent - 1 := by
  have honeToNat : (1 : PySSize).toNat = 1 := by decide
  have hone : (1 : PySSize) ≤ (1 : PySSize) <<< exponent := by
    rw [BitVec.le_def, one_shift_toNat (by omega)]
    simpa using Nat.one_le_two_pow
  rw [BitVec.toNat_sub_of_le hone, one_shift_toNat (by omega)]
  rw [honeToNat]

end CPythonListsort

namespace CPythonListsort

/--
[cIntMinrunMask_toNat_lt_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
lemma cIntMinrunMask_toNat_lt_pow
  {exponent : Nat} :
-- imply
  (((((1 : BitVec 32) <<< exponent) - 1).zeroExtend 64).toNat) < 2 ^ exponent := by
-- proof
  by_cases hexponent : exponent < 32
  · rw [cIntMask_eq_fullMask hexponent, mask_toNat hexponent]
    exact Nat.sub_lt (pow_pos (by omega) _) (by omega)
  · rw [BitVec.toNat_setWidth_of_le (by omega)]
    have hmask32 : ((((1 : BitVec 32) <<< exponent) - 1).toNat) < 2 ^ 32 :=
      ((((1 : BitVec 32) <<< exponent) - 1).isLt)
    have hpow : 2 ^ 32 ≤ 2 ^ exponent :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

end CPythonListsort

namespace CPythonListsort

/--
[minrunNext_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Minrun.lean)
-/
@[path]
lemma minrunNext_eq_spec
  {state : MinrunState}
-- given
  (hexponent : state.mr_e.toNat < 32)
  (hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1)
  (hnoOverflow : state.mr_current.toNat + state.listlen.toNat < 2 ^ 63) :
-- imply
  let specified := minrunNextSpec state.listlen.toNat state.mr_current.toNat state.mr_e.toNat (minrunNext state).result.toNat = specified.result ∧ (minrunNext state).state.mr_current.toNat = specified.residual ∧ (minrunNext state).assertionPassed = true := by
-- proof
  let total : PySSize := state.mr_current + state.listlen
  have htotal64 : state.mr_current.toNat + state.listlen.toNat < 2 ^ 64 := by
    norm_num at hnoOverflow ⊢
    omega
  have htotalNat : total.toNat = state.mr_current.toNat + state.listlen.toNat := by
    exact BitVec.toNat_add_of_lt htotal64
  have htotalMbs : total.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, htotalNat]
    norm_num at hnoOverflow ⊢
    omega
  dsimp [minrunNextSpec]
  constructor
  · simp only [minrunNext, total, BitVec.toNat_sshiftRight_of_msb_false htotalMbs,
    htotalNat, Nat.shiftRight_eq_div_pow]
  constructor
  · change (total &&& state.mr_mask).toNat =
    (state.mr_current.toNat + state.listlen.toNat) % 2 ^ state.mr_e.toNat
    rw [BitVec.toNat_and, hmask, mask_toNat hexponent,
      Nat.and_two_pow_sub_one_eq_mod, htotalNat]
  · simp [minrunNext, total, htotalMbs]

end CPythonListsort


-- created on 2026-10-23
