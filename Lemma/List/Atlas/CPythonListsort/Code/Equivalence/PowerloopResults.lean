import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Equivalence.PowerloopResults
open CPythonListsort


namespace CPythonListsort

/--
[powerloopInputBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopInputBounds
  {s1 n1 n2 n : PySSize}
-- given
  (hvalid : ValidPowerloopInput s1 n1 n2 n) :
-- imply
  let a := 2 * s1.toNat + n1.toNat let b := a + n1.toNat + n2.toNat 0 < n.toNat ∧ a < b ∧ b < 2 * n.toNat ∧ a < 2 ^ 63 ∧ b < 2 ^ 63 ∧ 2 * a < 2 ^ 63 ∧ 2 * b < 2 ^ 63 := by
-- proof
  obtain ⟨_, _, _, _, hn1, hn2, hsum, hnmax⟩ := hvalid
  rw [pyListMax_eq] at hnmax
  norm_num at hnmax ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatStep_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatStep_bounds
  {n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = false)
  (hbounds : PowerloopNatBounds n state) :
-- imply
  let next := powerloopNatStep n state next.stopped = true ∨ (next.stopped = false ∧ PowerloopNatBounds n next ∧ next.b - next.a = 2 * (state.b - state.a)) := by
-- proof
  obtain ⟨hn, hab, hbn⟩ := hbounds
  by_cases hna : n ≤ state.a
  · have hnb : n ≤ state.b := le_trans hna hab.le
    right
    simp [powerloopNatStep, hstopped, hna, PowerloopNatBounds]
    omega
  · by_cases hnb : n ≤ state.b
    · left
      simp [powerloopNatStep, hstopped, hna, hnb]
    · right
      simp [powerloopNatStep, hstopped, hna, hnb, PowerloopNatBounds]
      omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatStep_result](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatStep_result
  {n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = false) :
-- imply
  (powerloopNatStep n state).result = state.result + 1 := by
-- proof
  simp only [powerloopNatStep, hstopped, Bool.false_eq_true, if_false]
  split <;> split <;> simp_all
@[simp] theorem powerloopNatLoop_of_stopped (fuel n : Nat) (state : PowerloopNatState)
  (hstopped : state.stopped = true) :
  powerloopNatLoop fuel n state = state := by
  cases fuel <;> simp [powerloopNatLoop, hstopped]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatLoop_unstopped_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatLoop_unstopped_gap
  {fuel n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = false)
  (hbounds : PowerloopNatBounds n state) :
-- imply
  let out := powerloopNatLoop fuel n state out.stopped = false → PowerloopNatBounds n out ∧ out.result = state.result + fuel ∧ out.b - out.a = 2 ^ fuel * (state.b - state.a) := by
-- proof
  induction fuel generalizing state with
  | zero =>
    simp [powerloopNatLoop, hbounds, hstopped]
  | succ fuel ih =>
    simp only [powerloopNatLoop, hstopped, Bool.false_eq_true, if_false]
    let next := powerloopNatStep n state
    have hstep := powerloopNatStep_bounds n state hstopped hbounds
    change next.stopped = true ∨
      (next.stopped = false ∧ PowerloopNatBounds n next ∧
        next.b - next.a = 2 * (state.b - state.a)) at hstep
    obtain hnext | ⟨hnext, hnextBounds, hgap⟩ := hstep
    · rw [powerloopNatLoop_of_stopped fuel n next hnext]
      simp [hnext]
    · intro hout
      have htail := ih next hnext hnextBounds hout
      obtain ⟨houtBounds, hresult, htailGap⟩ := htail
      refine ⟨houtBounds, ?_, ?_⟩
      · have hstepResult : next.result = state.result + 1 := by
        simpa [next] using powerloopNatStep_result n state hstopped
        change (powerloopNatLoop fuel n next).result = state.result + (fuel + 1)
        omega
      · rw [htailGap, hgap, Nat.pow_succ]
        ac_rfl

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatLoop_result_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatLoop_result_le
  {fuel n : Nat}
  {state : PowerloopNatState} :
-- imply
  (powerloopNatLoop fuel n state).result ≤ state.result + fuel := by
-- proof
  induction fuel generalizing state with
  | zero => simp [powerloopNatLoop]
  | succ fuel ih =>
    cases hstopped : state.stopped with
    | true => simp [powerloopNatLoop, hstopped]
    | false =>
      simp only [powerloopNatLoop, hstopped, Bool.false_eq_true, if_false]
      have htail := ih (powerloopNatStep n state)
      have hstep := powerloopNatStep_result n state hstopped
      omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatLoop_stops_by_sixty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatLoop_stops_by_sixty
  {n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = false)
  (hbounds : PowerloopNatBounds n state)
  (hgap : 2 ≤ state.b - state.a)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  (powerloopNatLoop 60 n state).stopped = true := by
-- proof
  by_contra hnot
  have houtFalse : (powerloopNatLoop 60 n state).stopped = false := by
    cases h : (powerloopNatLoop 60 n state).stopped <;> simp_all
  have hrun := powerloopNatLoop_unstopped_gap 60 n state hstopped hbounds houtFalse
  obtain ⟨houtBounds, _, houtGap⟩ := hrun
  obtain ⟨_, houtAB, houtBN⟩ := houtBounds
  rw [pyListMax_eq] at hnmax
  norm_num at houtGap hnmax
  have hgapUpper :
    (powerloopNatLoop 60 n state).b - (powerloopNatLoop 60 n state).a < 2 * n := by
    omega
  omega

end CPythonListsort

namespace CPythonListsort

/--
[pySSize_nonnegative_of_double_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
private lemma pySSize_nonnegative_of_double_lt (x : PySSize)
  (hfit : 2 * x.toNat < 2 ^ 63) : x.Nonnegative := by
  rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
  norm_num at hfit ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopTraceSafe_of_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopTraceSafe_of_bounds
  {fuel : Nat}
  {n : PySSize}
  {state : PowerloopState}
-- given
  (hn : n.Nonnegative)
  (hnmax : n.toNat ≤ PY_LIST_MAX)
  (hstopped : state.stopped = false)
  (hbounds : PowerloopNatBounds n.toNat state.toNatState) :
-- imply
  PowerloopTraceSafe fuel n state := by
-- proof
  induction fuel generalizing state with
  | zero => trivial
  | succ fuel ih =>
    obtain ⟨hnpos, hab, hbn⟩ := hbounds
    change state.a.toNat < state.b.toNat at hab
    change state.b.toNat < 2 * n.toNat at hbn
    have hbFit : 2 * state.b.toNat < 2 ^ 63 := by
      rw [pyListMax_eq] at hnmax
      norm_num at hnmax ⊢
      omega
    have haFit : 2 * state.a.toNat < 2 ^ 63 := by omega
    have haNonnegative := pySSize_nonnegative_of_double_lt state.a haFit
    have hbNonnegative := pySSize_nonnegative_of_double_lt state.b hbFit
    have hsafe : PowerloopStepSafe n state :=
      ⟨hn, haNonnegative, hbNonnegative, hab.le, haFit, hbFit⟩
    simp only [PowerloopTraceSafe, hstopped, Bool.false_eq_true, if_false]
    refine ⟨hsafe, ?_⟩
    have heq := powerloopStep_eq_spec n state hsafe
    have hstateStopped : state.toNatState.stopped = false := by
      simpa [PowerloopState.toNatState] using hstopped
    have hstep := powerloopNatStep_bounds n.toNat state.toNatState
      hstateStopped ⟨hnpos, hab, hbn⟩
    have hstoppedEq := congrArg (fun s : PowerloopNatState => s.stopped) heq
    obtain hnextStopped | ⟨hnextRunning, hnextBounds, _⟩ := hstep
    · have hbitStopped : (powerloopStep n state).stopped = true := by
      change (powerloopStep n state).toNatState.stopped = true
      exact hstoppedEq.trans hnextStopped
      cases fuel <;> simp [PowerloopTraceSafe, hbitStopped]
    · have hbitRunning : (powerloopStep n state).stopped = false := by
      change (powerloopStep n state).toNatState.stopped = false
      exact hstoppedEq.trans hnextRunning
      apply ih (powerloopStep n state) hbitRunning
      rwa [heq]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopInitial_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopInitial_toNat
  {s1 n1 n2 n : PySSize}
-- given
  (hvalid : ValidPowerloopInput s1 n1 n2 n) :
-- imply
  let a : PySSize := 2 * s1 + n1 let b : PySSize := a + n1 + n2 a.toNat = 2 * s1.toNat + n1.toNat ∧ b.toNat = 2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat := by
-- proof
  have hbounds := powerloopInputBounds s1 n1 n2 n hvalid
  dsimp only at hbounds ⊢
  obtain ⟨_, _, _, ha, hb, _, _⟩ := hbounds
  have htwo : (2 : PySSize).toNat = 2 := by decide
  have hmul : ((2 : PySSize) * s1).toNat = 2 * s1.toNat := by
    apply BitVec.toNat_mul_of_lt
    rw [htwo]
    norm_num at ha ⊢
    omega
  have haNat : (2 * s1 + n1).toNat = 2 * s1.toNat + n1.toNat := by
    calc
      (2 * s1 + n1).toNat = (2 * s1).toNat + n1.toNat :=
        BitVec.toNat_add_of_lt (by rw [hmul]; norm_num at ha ⊢; omega)
      _ = 2 * s1.toNat + n1.toNat := by rw [hmul]
  have habNat : ((2 * s1 + n1) + n1).toNat =
    2 * s1.toNat + n1.toNat + n1.toNat := by
    calc
      ((2 * s1 + n1) + n1).toNat = (2 * s1 + n1).toNat + n1.toNat :=
        BitVec.toNat_add_of_lt (by rw [haNat]; norm_num at hb ⊢; omega)
      _ = 2 * s1.toNat + n1.toNat + n1.toNat := by rw [haNat]
  constructor
  · exact haNat
  · calc
    ((2 * s1 + n1) + n1 + n2).toNat =
      ((2 * s1 + n1) + n1).toNat + n2.toNat :=
      BitVec.toNat_add_of_lt (by rw [habNat]; norm_num at hb ⊢; omega)
    _ = 2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat := by rw [habNat]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopTraceSafetyCore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
private lemma powerloopTraceSafetyCore (s1 n1 n2 n : PySSize)
  (hvalid : ValidPowerloopInput s1 n1 n2 n) :
  let a := 2 * s1 + n1
  let b := a + n1 + n2
  PowerloopTraceSafe 64 n { result := 0, a := a, b := b, stopped := false } := by
  obtain ⟨hs1, hn1, hn2, hn, hn1pos, hn2pos, hsum, hnmax⟩ := hvalid
  have hvalid' : ValidPowerloopInput s1 n1 n2 n :=
    ⟨hs1, hn1, hn2, hn, hn1pos, hn2pos, hsum, hnmax⟩
  have hbounds := powerloopInputBounds s1 n1 n2 n hvalid'
  have hinit := powerloopInitial_toNat s1 n1 n2 n hvalid'
  dsimp only at hbounds hinit ⊢
  obtain ⟨hnpos, hab, hbn, _, _, _, _⟩ := hbounds
  obtain ⟨haNat, hbNat⟩ := hinit
  apply powerloopTraceSafe_of_bounds 64 n _ hn hnmax rfl
  simp only [PowerloopState.toNatState]
  rw [haNat, hbNat]
  exact ⟨hnpos, hab, hbn⟩

end CPythonListsort

namespace CPythonListsort

/--
[powerloopQuotientBit_eq_residue_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopQuotientBit_eq_residue_div
  {x n k : Nat} :
-- imply
  powerloopQuotientBit x n k = powerloopResidue x n k / n := by
-- proof
  unfold powerloopQuotientBit powerloopResidue
  rw [← Nat.mod_mul_right_div_self]
  congr 2
  omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopResidue_succ_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
private lemma powerloopResidue_succ_base (x n k : Nat) :
  powerloopResidue x n (k + 1) =
    (2 * powerloopResidue x n k) % (2 * n) := by
  unfold powerloopResidue
  rw [Nat.pow_succ]
  have hmul : 2 ^ k * 2 * x = 2 * (2 ^ k * x) := by ring
  rw [hmul]
  simp only [Nat.mul_mod, Nat.mod_mod]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopResidue_succ_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopResidue_succ_of_lt
  {x n k : Nat}
-- given
  (hres : powerloopResidue x n k < n) :
-- imply
  powerloopResidue x n (k + 1) = 2 * powerloopResidue x n k := by
-- proof
  rw [powerloopResidue_succ_base]
  rw [Nat.mod_eq_of_lt]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopResidue_succ_of_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopResidue_succ_of_ge
  {x n k : Nat}
-- given
  (hn : 0 < n)
  (hge : n ≤ powerloopResidue x n k) :
-- imply
  powerloopResidue x n (k + 1) = 2 * (powerloopResidue x n k - n) := by
-- proof
  have hmodulus : 0 < 2 * n := by omega
  have hreslt : powerloopResidue x n k < 2 * n := by
    exact Nat.mod_lt _ hmodulus
  rw [powerloopResidue_succ_base]
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[powerloopQuotientBit_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopQuotientBit_eq_zero_iff
  {x n k : Nat}
-- given
  (hn : 0 < n) :
-- imply
  powerloopQuotientBit x n k = 0 ↔ powerloopResidue x n k < n := by
-- proof
  rw [powerloopQuotientBit_eq_residue_div]
  constructor
  · intro hzero
    by_contra hnot
    have hge : n ≤ powerloopResidue x n k := by omega
    have hlt : powerloopResidue x n k < 2 * n :=
      Nat.mod_lt _ (by omega)
    have hone : powerloopResidue x n k / n = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) hlt
    omega
  · intro hlt
    exact Nat.div_eq_of_lt hlt

end CPythonListsort

namespace CPythonListsort

/--
[powerloopQuotientBit_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopQuotientBit_eq_one_iff
  {x n k : Nat}
-- given
  (hn : 0 < n) :
-- imply
  powerloopQuotientBit x n k = 1 ↔ n ≤ powerloopResidue x n k := by
-- proof
  rw [powerloopQuotientBit_eq_residue_div]
  constructor
  · intro hone
    by_contra hnot
    have hzero : powerloopResidue x n k / n = 0 :=
      Nat.div_eq_of_lt (by omega)
    omega
  · intro hge
    have hlt : powerloopResidue x n k < 2 * n :=
      Nat.mod_lt _ (by omega)
    exact Nat.div_eq_of_lt_le (by omega) hlt

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatQuotientInvariant_init](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatQuotientInvariant_init
  {a b n : Nat}
-- given
  (ha : a < 2 * n)
  (hb : b < 2 * n) :
-- imply
  PowerloopNatQuotientInvariant a b n { result := 0, a := a, b := b, stopped := false } := by
-- proof
  simp [PowerloopNatQuotientInvariant, powerloopResidue, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatQuotientInvariant_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatQuotientInvariant_step
  {a b n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = false)
  (hbounds : PowerloopNatBounds n state)
  (hinvariant : PowerloopNatQuotientInvariant a b n state) :
-- imply
  PowerloopNatQuotientInvariant a b n (powerloopNatStep n state) := by
-- proof
  obtain ⟨hn, hab, hbn⟩ := hbounds
  simp only [PowerloopNatQuotientInvariant, hstopped, Bool.false_eq_true, if_false] at hinvariant
  obtain ⟨k, hresult, haState, hbState, hprior⟩ := hinvariant
  by_cases hna : n ≤ state.a
  · have hnb : n ≤ state.b := le_trans hna hab.le
    have haBit : powerloopQuotientBit a n k = 1 := by
      rw [powerloopQuotientBit_eq_one_iff a n k hn]
      rwa [← haState]
    have hbBit : powerloopQuotientBit b n k = 1 := by
      rw [powerloopQuotientBit_eq_one_iff b n k hn]
      rwa [← hbState]
    have haNext := powerloopResidue_succ_of_ge a n k hn (by rwa [← haState])
    have hbNext := powerloopResidue_succ_of_ge b n k hn (by rwa [← hbState])
    simp only [powerloopNatStep, hstopped, Bool.false_eq_true, if_false, hna, if_true]
    simp only [PowerloopNatQuotientInvariant, Bool.false_eq_true, if_false]
    refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
    · simpa [haState] using haNext.symm
    · simpa [hbState] using hbNext.symm
    · intro j hj
      by_cases hjk : j < k
      · exact hprior j hjk
      · have hjEq : j = k := by omega
        subst j
        rw [haBit, hbBit]
  · by_cases hnb : n ≤ state.b
    · have haBit : powerloopQuotientBit a n k = 0 := by
      rw [powerloopQuotientBit_eq_zero_iff a n k hn]
      rw [← haState]
      omega
      have hbBit : powerloopQuotientBit b n k = 1 := by
        rw [powerloopQuotientBit_eq_one_iff b n k hn]
        rwa [← hbState]
      simp only [powerloopNatStep, hstopped, Bool.false_eq_true, if_false, hna, hnb,
        if_true, PowerloopNatQuotientInvariant]
      exact ⟨k, by omega, haBit, hbBit, hprior⟩
    · have haBit : powerloopQuotientBit a n k = 0 := by
      rw [powerloopQuotientBit_eq_zero_iff a n k hn]
      rw [← haState]
      omega
      have hbBit : powerloopQuotientBit b n k = 0 := by
        rw [powerloopQuotientBit_eq_zero_iff b n k hn]
        rw [← hbState]
        omega
      have haNext := powerloopResidue_succ_of_lt a n k (by rw [← haState]; omega)
      have hbNext := powerloopResidue_succ_of_lt b n k (by rw [← hbState]; omega)
      simp only [powerloopNatStep, hstopped, Bool.false_eq_true, if_false, hna, hnb]
      simp only [PowerloopNatQuotientInvariant, Bool.false_eq_true, if_false]
      refine ⟨k + 1, by omega, ?_, ?_, ?_⟩
      · simpa [haState] using haNext.symm
      · simpa [hbState] using hbNext.symm
      · intro j hj
        by_cases hjk : j < k
        · exact hprior j hjk
        · have hjEq : j = k := by omega
          subst j
          rw [haBit, hbBit]

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatQuotientInvariant_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatQuotientInvariant_loop
  {fuel a b n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = false)
  (hbounds : PowerloopNatBounds n state)
  (hinvariant : PowerloopNatQuotientInvariant a b n state) :
-- imply
  PowerloopNatQuotientInvariant a b n (powerloopNatLoop fuel n state) := by
-- proof
  induction fuel generalizing state with
  | zero => simpa [powerloopNatLoop] using hinvariant
  | succ fuel ih =>
    simp only [powerloopNatLoop, hstopped, Bool.false_eq_true, if_false]
    let next := powerloopNatStep n state
    have hnextInvariant :=
      powerloopNatQuotientInvariant_step a b n state hstopped hbounds hinvariant
    have hstep := powerloopNatStep_bounds n state hstopped hbounds
    change next.stopped = true ∨
      (next.stopped = false ∧ PowerloopNatBounds n next ∧
        next.b - next.a = 2 * (state.b - state.a)) at hstep
    obtain hnextStopped | ⟨hnextRunning, hnextBounds, _⟩ := hstep
    · rw [powerloopNatLoop_of_stopped fuel n next hnextStopped]
      exact hnextInvariant
    · exact ih next hnextRunning hnextBounds hnextInvariant

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatLoop_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatLoop_add
  {first second n : Nat}
  {state : PowerloopNatState} :
-- imply
  powerloopNatLoop (first + second) n state = powerloopNatLoop second n (powerloopNatLoop first n state) := by
-- proof
  induction first generalizing state with
  | zero => simp [powerloopNatLoop]
  | succ first ih =>
    cases hstopped : state.stopped with
    | true => simp [powerloopNatLoop, hstopped]
    | false =>
      simp only [Nat.succ_add, powerloopNatLoop, hstopped, Bool.false_eq_true, if_false]
      exact ih (powerloopNatStep n state)

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatResult_of_gap_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatResult_of_gap_two
  {a b n : Nat}
-- given
  (hn : 0 < n)
  (hab : a < b)
  (hbn : b < 2 * n)
  (hgap : 2 ≤ b - a)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  let initial : PowerloopNatState := { result := 0, a := a, b := b, stopped := false } let out := powerloopNatLoop 64 n initial out.stopped = true ∧ ∃ k < 60, out.result = k + 1 ∧ IsFirstDifferingQuotientBit a b n k := by
-- proof
  let initial : PowerloopNatState :=
    { result := 0, a := a, b := b, stopped := false }
  have hbounds : PowerloopNatBounds n initial := ⟨hn, hab, hbn⟩
  have hstop60 := powerloopNatLoop_stops_by_sixty n initial rfl hbounds hgap hnmax
  have houtEq : powerloopNatLoop 64 n initial = powerloopNatLoop 60 n initial := by
    calc
      powerloopNatLoop 64 n initial = powerloopNatLoop (60 + 4) n initial := by norm_num
      _ = powerloopNatLoop 4 n (powerloopNatLoop 60 n initial) :=
        powerloopNatLoop_add 60 4 n initial
      _ = powerloopNatLoop 60 n initial :=
        powerloopNatLoop_of_stopped 4 n _ hstop60
  have hstop64 : (powerloopNatLoop 64 n initial).stopped = true := by
    rwa [houtEq]
  have hinitialInvariant : PowerloopNatQuotientInvariant a b n initial := by
    exact powerloopNatQuotientInvariant_init a b n (by omega) hbn
  have houtInvariant := powerloopNatQuotientInvariant_loop 64 a b n initial
    rfl hbounds hinitialInvariant
  have hexists : ∃ k,
    (powerloopNatLoop 64 n initial).result = k + 1 ∧
      IsFirstDifferingQuotientBit a b n k := by
    simpa [PowerloopNatQuotientInvariant, hstop64] using houtInvariant
  obtain ⟨k, hresult, hfirst⟩ := hexists
  have hresultLe60 : (powerloopNatLoop 64 n initial).result ≤ 60 := by
    rw [houtEq]
    simpa [initial] using powerloopNatLoop_result_le 60 n initial
  exact ⟨hstop64, k, by omega, hresult, hfirst⟩

end CPythonListsort

namespace CPythonListsort

/--
[powerloopNatResult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopNatResult
  {a b n : Nat}
-- given
  (hn : 0 < n)
  (hab : a < b)
  (hbn : b < 2 * n)
  (hnmax : n ≤ PY_LIST_MAX) :
-- imply
  let initial : PowerloopNatState := { result := 0, a := a, b := b, stopped := false } let out := powerloopNatLoop 64 n initial out.stopped = true ∧ ∃ k < 61, out.result = k + 1 ∧ IsFirstDifferingQuotientBit a b n k := by
-- proof
  let initial : PowerloopNatState :=
    { result := 0, a := a, b := b, stopped := false }
  have hbounds : PowerloopNatBounds n initial := ⟨hn, hab, hbn⟩
  have hstop61 : (powerloopNatLoop 61 n initial).stopped = true := by
    by_contra hnot
    have houtFalse : (powerloopNatLoop 61 n initial).stopped = false := by
      cases h : (powerloopNatLoop 61 n initial).stopped <;> simp_all
    have hrun := powerloopNatLoop_unstopped_gap 61 n initial rfl hbounds houtFalse
    obtain ⟨houtBounds, _, houtGap⟩ := hrun
    obtain ⟨_, houtAB, houtBN⟩ := houtBounds
    rw [pyListMax_eq] at hnmax
    norm_num at houtGap hnmax
    have hgapInitial : 1 ≤ initial.b - initial.a := by
      simp [initial]
      omega
    have hgapUpper :
      (powerloopNatLoop 61 n initial).b - (powerloopNatLoop 61 n initial).a <
        2 * n := by
      omega
    omega
  have houtEq : powerloopNatLoop 64 n initial = powerloopNatLoop 61 n initial := by
    calc
      powerloopNatLoop 64 n initial = powerloopNatLoop (61 + 3) n initial := by norm_num
      _ = powerloopNatLoop 3 n (powerloopNatLoop 61 n initial) :=
        powerloopNatLoop_add 61 3 n initial
      _ = powerloopNatLoop 61 n initial :=
        powerloopNatLoop_of_stopped 3 n _ hstop61
  have hstop64 : (powerloopNatLoop 64 n initial).stopped = true := by
    rwa [houtEq]
  have hinitialInvariant : PowerloopNatQuotientInvariant a b n initial :=
    powerloopNatQuotientInvariant_init a b n (by omega) hbn
  have houtInvariant := powerloopNatQuotientInvariant_loop 64 a b n initial
    rfl hbounds hinitialInvariant
  have hexists : ∃ k,
    (powerloopNatLoop 64 n initial).result = k + 1 ∧
      IsFirstDifferingQuotientBit a b n k := by
    simpa [PowerloopNatQuotientInvariant, hstop64] using houtInvariant
  obtain ⟨k, hresult, hfirst⟩ := hexists
  have hresultLe61 : (powerloopNatLoop 64 n initial).result ≤ 61 := by
    rw [houtEq]
    simpa [initial] using powerloopNatLoop_result_le 61 n initial
  exact ⟨hstop64, k, by omega, hresult, hfirst⟩

end CPythonListsort

namespace CPythonListsort

/--
[powerloopResult](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopResult
  {s1 n1 n2 n : PySSize}
-- given
  (hvalid : ValidPowerloopInput s1 n1 n2 n) :
-- imply
  let a := 2 * s1.toNat + n1.toNat let b := a + n1.toNat + n2.toNat (powerloopTraced s1 n1 n2 n).stopped = true ∧ ∃ k < 60, powerloop s1 n1 n2 n = k + 1 ∧ IsFirstDifferingQuotientBit a b n.toNat k := by
-- proof
  have hbounds := powerloopInputBounds s1 n1 n2 n hvalid
  have htrace := powerloopTraceSafetyCore s1 n1 n2 n hvalid
  have hprojection :
    (powerloopTraced s1 n1 n2 n).toNatState = powerloopNatSpec s1 n1 n2 n := by
    apply powerloopTraced_eq_spec
    · simpa using hbounds.2.2.2.1
    · simpa [Nat.add_assoc] using hbounds.2.2.2.2.1
    · exact htrace
  dsimp only at hbounds ⊢
  obtain ⟨hn, hab, hbn, _, _, _, _⟩ := hbounds
  have hgap : 2 ≤
    (2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat) -
      (2 * s1.toNat + n1.toNat) := by
    obtain ⟨_, _, _, _, hn1, hn2, _, _⟩ := hvalid
    omega
  have hnat := powerloopNatResult_of_gap_two
    (2 * s1.toNat + n1.toNat)
    (2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat)
    n.toNat hn hab hbn hgap hvalid.2.2.2.2.2.2.2
  dsimp only [powerloopNatSpec] at hnat
  have hstoppedEq := congrArg (fun state : PowerloopNatState => state.stopped) hprojection
  have hresultEq := congrArg (fun state : PowerloopNatState => state.result) hprojection
  simp only [PowerloopState.toNatState] at hstoppedEq hresultEq
  obtain ⟨hnatStopped, k, hk, hnatResult, hfirst⟩ := hnat
  refine ⟨?_, k, hk, ?_, hfirst⟩
  · exact hstoppedEq.trans hnatStopped
  · unfold powerloop
    exact hresultEq.trans hnatResult

end CPythonListsort

namespace CPythonListsort

/--
[powerloopTraceSafety](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerloopTraceSafety
  {s1 n1 n2 n : PySSize}
-- given
  (hvalid : ValidPowerloopInput s1 n1 n2 n) :
-- imply
  let a := 2 * s1 + n1 let b := a + n1 + n2 PowerloopTraceSafe 64 n { result := 0, a := a, b := b, stopped := false } ∧ (powerloopTraced s1 n1 n2 n).stopped = true := by
-- proof
  exact ⟨powerloopTraceSafetyCore s1 n1 n2 n hvalid,
    (powerloopResult s1 n1 n2 n hvalid).1⟩

end CPythonListsort

namespace CPythonListsort

/--
[powerBound_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerBound_relation
-- imply
  POWER_BOUND + 1 = 61 ∧ 61 < MAX_MERGE_PENDING := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[powerRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
lemma powerRange
  {s1 n1 n2 n : PySSize}
-- given
  (hvalid : ValidPowerloopInput s1 n1 n2 n) :
-- imply
  1 ≤ powerloop s1 n1 n2 n ∧ powerloop s1 n1 n2 n ≤ POWER_BOUND ∧ POWER_BOUND + 1 < MAX_MERGE_PENDING := by
-- proof
  have hresult := powerloopResult s1 n1 n2 n hvalid
  dsimp only at hresult
  obtain ⟨_, k, hk, hpower, _⟩ := hresult
  constructor
  · omega
  constructor
  · simp only [POWER_BOUND]
    omega
  · exact powerBound_relation.2

end CPythonListsort

/--
[pyListMax_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
private lemma pyListMax_eq_eq :
-- imply
  PY_LIST_MAX = 2 ^ 60 - 1 := by
-- proof
  apply CPythonListsort.pyListMax_eq

/--
[powerloopNatLoop_of_stopped](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/PowerloopResults.lean)
-/
@[path]
private lemma powerloopNatLoop_of_stopped_eq
  {fuel n : Nat}
  {state : PowerloopNatState}
-- given
  (hstopped : state.stopped = true) :
-- imply
  powerloopNatLoop fuel n state = state := by
-- proof
  apply CPythonListsort.powerloopNatLoop_of_stopped fuel n state hstopped


-- created on 2026-10-23
