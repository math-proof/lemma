import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Equivalence.Powerloop
open CPythonListsort


namespace CPythonListsort

/--
[slt_eq_nat_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean)
-/
@[path]
private lemma slt_eq_nat_lt (x y : PySSize)
  (hx : x.Nonnegative) (hy : y.Nonnegative) :
  x.slt y = decide (x.toNat < y.toNat) := by
  rw [BitVec.slt_eq_decide]
  rw [BitVec.toInt_eq_toNat_of_msb hx]
  rw [BitVec.toInt_eq_toNat_of_msb hy]
  norm_cast

end CPythonListsort

namespace CPythonListsort

/--
[toNat_shiftLeft_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean)
-/
@[path]
private lemma toNat_shiftLeft_one (x : PySSize)
  (hfit : 2 * x.toNat < 2 ^ 63) :
  (x <<< 1).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  norm_num
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

end CPythonListsort

namespace CPythonListsort

/--
[toNat_two_mul_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean)
-/
@[path]
private lemma toNat_two_mul_add (x y : PySSize)
  (hfit : 2 * x.toNat + y.toNat < 2 ^ 63) :
  (2 * x + y).toNat = 2 * x.toNat + y.toNat := by
  have htwo : (2 : PySSize).toNat = 2 := by decide
  have hmul : ((2 : PySSize) * x).toNat = 2 * x.toNat := by
    apply BitVec.toNat_mul_of_lt
    rw [htwo]
    norm_num at hfit ⊢
    omega
  calc
    (2 * x + y).toNat = (2 * x).toNat + y.toNat :=
      BitVec.toNat_add_of_lt (by rw [hmul]; norm_num at hfit ⊢; omega)
    _ = 2 * x.toNat + y.toNat := by rw [hmul]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopStep_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean)
-/
@[path]
lemma powerloopStep_eq_spec
  {n : PySSize}
  {state : PowerloopState}
-- given
  (hsafe : PowerloopStepSafe n state) :
-- imply
  (powerloopStep n state).toNatState = powerloopNatStep n.toNat state.toNatState := by
-- proof
  obtain ⟨hn, haNonnegative, hbNonnegative, hab, haFit, hbFit⟩ := hsafe
  have haCmp := slt_eq_nat_lt state.a n haNonnegative hn
  have hbCmp := slt_eq_nat_lt state.b n hbNonnegative hn
  cases hstopped : state.stopped with
  | true =>
    simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState, hstopped]
  | false =>
    by_cases hna : n.toNat ≤ state.a.toNat
    · have hnb : n.toNat ≤ state.b.toNat := le_trans hna hab
      have hnaBits : n ≤ state.a := by simpa [BitVec.le_def] using hna
      have hnbBits : n ≤ state.b := by simpa [BitVec.le_def] using hnb
      have haSubFit : 2 * (state.a - n).toNat < 2 ^ 63 := by
        rw [BitVec.toNat_sub_of_le hnaBits]
        omega
      have hbSubFit : 2 * (state.b - n).toNat < 2 ^ 63 := by
        rw [BitVec.toNat_sub_of_le hnbBits]
        omega
      simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState,
        hstopped, haCmp, hna, BitVec.toNat_sub_of_le hnaBits,
        BitVec.toNat_sub_of_le hnbBits,
        toNat_shiftLeft_one (state.a - n) haSubFit,
        toNat_shiftLeft_one (state.b - n) hbSubFit]
    · by_cases hnb : n.toNat ≤ state.b.toNat
      · simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState,
        hstopped, haCmp, hbCmp, hna, hnb]
      · simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState,
        hstopped, haCmp, hbCmp, hna, hnb,
        toNat_shiftLeft_one state.a haFit,
        toNat_shiftLeft_one state.b hbFit]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopLoop_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean)
-/
@[path]
lemma powerloopLoop_eq_spec
  {fuel : Nat}
  {n : PySSize}
  {state : PowerloopState}
-- given
  (hsafe : PowerloopTraceSafe fuel n state) :
-- imply
  (powerloopLoop fuel n state).toNatState = powerloopNatLoop fuel n.toNat state.toNatState := by
-- proof
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    cases hstopped : state.stopped with
    | true =>
      simp [powerloopLoop, powerloopNatLoop, PowerloopState.toNatState, hstopped]
    | false =>
      have hsafePair :
        PowerloopStepSafe n state ∧
          PowerloopTraceSafe fuel n (powerloopStep n state) := by
        simpa [PowerloopTraceSafe, hstopped] using hsafe
      have hsafeStep : PowerloopStepSafe n state := by
        exact hsafePair.1
      have hsafeTail : PowerloopTraceSafe fuel n (powerloopStep n state) := by
        exact hsafePair.2
      simp only [powerloopLoop, powerloopNatLoop, hstopped, Bool.false_eq_true,
        if_false]
      rw [ih (powerloopStep n state) hsafeTail]
      rw [powerloopStep_eq_spec n state hsafeStep]
      simp [PowerloopState.toNatState, hstopped]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopTraced_eq_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/Powerloop.lean)
-/
@[path]
lemma powerloopTraced_eq_spec
  {s1 n1 n2 n : PySSize}
-- given
  (haInit : 2 * s1.toNat + n1.toNat < 2 ^ 63)
  (hbInit : 2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat < 2 ^ 63)
  (hsafe : let a := 2 * s1 + n1 let b := a + n1 + n2 PowerloopTraceSafe 64 n { result := 0, a := a, b := b, stopped := false }) :
-- imply
  (powerloopTraced s1 n1 n2 n).toNatState = powerloopNatSpec s1 n1 n2 n := by
-- proof
  have haNat : (2 * s1 + n1).toNat = 2 * s1.toNat + n1.toNat :=
    toNat_two_mul_add s1 n1 haInit
  have habNat : ((2 * s1 + n1) + n1).toNat =
    2 * s1.toNat + n1.toNat + n1.toNat := by
    calc
      ((2 * s1 + n1) + n1).toNat = (2 * s1 + n1).toNat + n1.toNat :=
        BitVec.toNat_add_of_lt (by rw [haNat]; norm_num at hbInit ⊢; omega)
      _ = 2 * s1.toNat + n1.toNat + n1.toNat := by rw [haNat]
  have hbNat : ((2 * s1 + n1) + n1 + n2).toNat =
    2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat := by
    calc
      ((2 * s1 + n1) + n1 + n2).toNat =
        ((2 * s1 + n1) + n1).toNat + n2.toNat :=
        BitVec.toNat_add_of_lt (by rw [habNat]; norm_num at hbInit ⊢; omega)
      _ = 2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat := by rw [habNat]
  unfold powerloopTraced powerloopNatSpec
  rw [powerloopLoop_eq_spec 64 n _ hsafe]
  simp only [PowerloopState.toNatState]
  rw [haNat, hbNat]

end CPythonListsort


-- created on 2026-10-23
