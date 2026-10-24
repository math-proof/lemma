/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import sympy.atlas.CPythonListsort.Code.Equivalence.Minrun
import sympy.atlas.CPythonListsort.Code.Equivalence.PowerloopResults
import Mathlib

/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/

namespace CPythonListsort

/-- Width-independent facts preserved by every adaptive-minrun call. -/
private structure MinrunRangeInv (state : MinrunState) : Prop where
  listMax : state.listlen.toNat ≤ PY_LIST_MAX
  exponent60 : state.mr_e.toNat ≤ 60
  current : state.mr_current.toNat < 2 ^ state.mr_e.toNat
  mask : state.mr_mask.toNat < 2 ^ state.mr_e.toNat
  modulusLe : 2 ^ state.mr_e.toNat ≤ state.listlen.toNat
  floorLt : state.listlen.toNat / 2 ^ state.mr_e.toNat < 64

/-- One adaptive-minrun call passes its assertion, returns a target in the
public `1 .. MAX_MINRUN` band, and preserves the bounded-current fact. -/
private theorem minrunNext_range (state : MinrunState)
    (h : MinrunRangeInv state) :
    (minrunNext state).assertionPassed = true ∧
      1 ≤ (minrunNext state).result.toNat ∧
      (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat ∧
      (minrunNext state).state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
  let total : PySSize := state.mr_current + state.listlen
  have hpowLe : 2 ^ state.mr_e.toNat ≤ 2 ^ 60 :=
    Nat.pow_le_pow_right (by omega) h.exponent60
  have hcurrent := h.current
  have hmodulusLe := h.modulusLe
  have hfloorLt := h.floorLt
  have hlistMax := h.listMax
  rw [pyListMax_eq] at hlistMax
  have htotal64 : state.mr_current.toNat + state.listlen.toNat < 2 ^ 64 := by
    norm_num at hpowLe hlistMax ⊢
    omega
  have htotal63 : state.mr_current.toNat + state.listlen.toNat < 2 ^ 63 := by
    norm_num at hpowLe hlistMax ⊢
    omega
  have htotalNat : total.toNat =
      state.mr_current.toNat + state.listlen.toNat :=
    BitVec.toNat_add_of_lt htotal64
  have htotalMsb : total.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, htotalNat]
    norm_num at htotal63 ⊢
    omega
  have hresult : (minrunNext state).result.toNat =
      (state.mr_current.toNat + state.listlen.toNat) /
        2 ^ state.mr_e.toNat := by
    simp only [minrunNext, total,
      BitVec.toNat_sshiftRight_of_msb_false htotalMsb,
      htotalNat, Nat.shiftRight_eq_div_pow]
  have hpowPositive : 0 < 2 ^ state.mr_e.toNat := by positivity
  have hpositive : 1 ≤ (minrunNext state).result.toNat := by
    rw [hresult]
    apply (Nat.le_div_iff_mul_le hpowPositive).2
    simp only [one_mul]
    omega
  have hlistLt : state.listlen.toNat < 64 * 2 ^ state.mr_e.toNat :=
    (Nat.div_lt_iff_lt_mul hpowPositive).mp hfloorLt
  have hupper : (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat := by
    have hresultLt : (minrunNext state).result.toNat < 65 := by
      rw [hresult]
      apply (Nat.div_lt_iff_lt_mul hpowPositive).2
      omega
    have hmaxMinrun : MAX_MINRUN.toNat = 64 := by decide
    rw [hmaxMinrun]
    omega
  have hnextCurrent :
      (minrunNext state).state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    simp only [minrunNext]
    rw [BitVec.toNat_and]
    exact Nat.and_lt_two_pow _ h.mask
  exact ⟨by simp [minrunNext, total, htotalMsb], hpositive, hupper,
    hnextCurrent⟩

private theorem MinrunRangeInv.next
    {state : MinrunState} (h : MinrunRangeInv state) :
    MinrunRangeInv (minrunNext state).state := by
  have hstep := minrunNext_range state h
  constructor
  · simpa [minrunNext] using h.listMax
  · simpa [minrunNext] using h.exponent60
  · simpa [minrunNext] using hstep.2.2.2
  · simpa [minrunNext] using h.mask
  · simpa [minrunNext] using h.modulusLe
  · simpa [minrunNext] using h.floorLt

/-- Iteration preserves the private range invariant and records the band for
every emitted target. -/
private theorem minrunNextN_range
    (calls : Nat) (state : MinrunState) (h : MinrunRangeInv state) :
    let run := minrunNextN calls state
    MinrunRangeInv run.state ∧
      run.assertionsPassed = true ∧
      ∀ target ∈ run.outputs,
        1 ≤ target ∧ target ≤ MAX_MINRUN.toNat := by
  induction calls generalizing state with
  | zero =>
      simp only [minrunNextN]
      exact ⟨h, trivial, by simp⟩
  | succ calls ih =>
      let next := minrunNext state
      have hstep := minrunNext_range state h
      have htail := ih next.state h.next
      dsimp only at htail
      rcases htail with ⟨htailInv, htailAssertions, htailBounds⟩
      simp only [minrunNextN]
      refine ⟨htailInv, ?_, ?_⟩
      · simp [next, hstep.1, htailAssertions]
      · intro target htarget
        simp only [List.mem_cons] at htarget
        rcases htarget with rfl | htarget
        · exact ⟨hstep.2.1, hstep.2.2.1⟩
        · exact htailBounds target htarget

/-- Arbitrarily many calls from `merge_init` pass every signed-overflow
assertion and emit only targets in `1 .. 64`.
This theorem does not use exact quotient/remainder mask equivalence. -/
theorem minrunNextN_output_bounds
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat)
    (calls : Nat) :
    let run := minrunNextN calls (minrunInit listSize)
    run.assertionsPassed = true ∧
      ∀ target ∈ run.outputs,
        1 ≤ target ∧ target ≤ MAX_MINRUN.toNat := by
  have hrun := minrunNextN_range calls (minrunInit listSize)
    (minrunInit_rangeInv listSize hNonnegative hMax hPositive)
  exact hrun.2

/-- The next call after any reachable prefix passes its assertion and returns
a target in the unconditional `1 .. MAX_MINRUN` band. -/
theorem minrunNext_after_init_bounds
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat)
    (calls : Nat) :
    let state := (minrunNextN calls (minrunInit listSize)).state
    (minrunNext state).assertionPassed = true ∧
      1 ≤ (minrunNext state).result.toNat ∧
      (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat := by
  have hrun := minrunNextN_range calls (minrunInit listSize)
    (minrunInit_rangeInv listSize hNonnegative hMax hPositive)
  dsimp only at hrun ⊢
  have hstep := minrunNext_range
    (minrunNextN calls (minrunInit listSize)).state hrun.1
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1⟩

/-- Natural-number trace of repeated quotient/remainder generator steps. -/
structure MinrunSpecTrace where
  outputs : List Nat
  residual : Nat
  deriving DecidableEq, Repr

/-- Iterate the exact-arithmetic minrun recurrence. -/
def minrunSpecTrace : Nat → Nat → Nat → Nat → MinrunSpecTrace
  | 0, _, _, current => { outputs := [], residual := current }
  | calls + 1, listlen, exponent, current =>
      let next := minrunNextSpec listlen current exponent
      let tail := minrunSpecTrace calls listlen exponent next.residual
      { outputs := next.result :: tail.outputs, residual := tail.residual }

/-- Repeated finite-width calls agree with the exact trace while preserving the C assertion. -/
theorem minrunNextN_eq_spec (calls : Nat) (state : MinrunState)
    (hexponent : state.mr_e.toNat < 32)
    (hexponent60 : state.mr_e.toNat ≤ 60)
    (hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1)
    (hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat)
    (hlistMax : state.listlen.toNat ≤ PY_LIST_MAX) :
    let trace := minrunSpecTrace calls state.listlen.toNat
      state.mr_e.toNat state.mr_current.toNat
    (minrunNextN calls state).outputs = trace.outputs ∧
      (minrunNextN calls state).state.mr_current.toNat = trace.residual ∧
      (minrunNextN calls state).assertionsPassed = true := by
  induction calls generalizing state with
  | zero => simp [minrunNextN, minrunSpecTrace]
  | succ calls ih =>
      have hpowLe : 2 ^ state.mr_e.toNat ≤ 2 ^ 60 :=
        Nat.pow_le_pow_right (by omega) hexponent60
      have hnoOverflow : state.mr_current.toNat + state.listlen.toNat < 2 ^ 63 := by
        rw [pyListMax_eq] at hlistMax
        norm_num at hpowLe hlistMax ⊢
        omega
      have hstep := minrunNext_eq_spec state hexponent hmask hnoOverflow
      let next := minrunNext state
      let specified := minrunNextSpec state.listlen.toNat state.mr_current.toNat
        state.mr_e.toNat
      change next.result.toNat = specified.result ∧
        next.state.mr_current.toNat = specified.residual ∧
        next.assertionPassed = true at hstep
      rcases hstep with ⟨hresult, hresidual, hassertion⟩
      have hnextExponent : next.state.mr_e.toNat = state.mr_e.toNat := by
        simp [next, minrunNext]
      have hnextMask :
          next.state.mr_mask = ((1 : PySSize) <<< next.state.mr_e.toNat) - 1 := by
        simp [next, minrunNext, hmask]
      have hnextList : next.state.listlen.toNat = state.listlen.toNat := by
        simp [next, minrunNext]
      have hnextCurrent : next.state.mr_current.toNat < 2 ^ next.state.mr_e.toNat := by
        rw [hnextExponent, hresidual]
        exact Nat.mod_lt _ (pow_pos (by omega) _)
      have htail := ih next.state
        (by rwa [hnextExponent])
        (by rwa [hnextExponent])
        hnextMask hnextCurrent (by rwa [hnextList])
      change
        next.result.toNat :: (minrunNextN calls next.state).outputs =
            specified.result ::
              (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
                specified.residual).outputs ∧
          (minrunNextN calls next.state).state.mr_current.toNat =
            (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
              specified.residual).residual ∧
          (next.assertionPassed && (minrunNextN calls next.state).assertionsPassed) = true
      rw [hresult]
      have htail' :
          (minrunNextN calls next.state).outputs =
              (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
                specified.residual).outputs ∧
            (minrunNextN calls next.state).state.mr_current.toNat =
              (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
                specified.residual).residual ∧
            (minrunNextN calls next.state).assertionsPassed = true := by
        simpa [hnextExponent, hnextList, hresidual] using htail
      rcases htail' with ⟨houtputs, htailResidual, htailAssertions⟩
      simp [houtputs, htailResidual, hassertion, htailAssertions]

/-- Ceiling division used to state the balanced-sequence result without rationals. -/
def minrunCeilDiv (x modulus : Nat) : Nat :=
  (x + modulus - 1) / modulus

private theorem minrunNextSpec_balanced (listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent) :
    let next := minrunNextSpec listlen current exponent
    next.result = listlen / 2 ^ exponent ∨
      next.result = minrunCeilDiv listlen (2 ^ exponent) := by
  let modulus := 2 ^ exponent
  let quotient := listlen / modulus
  let residual := listlen % modulus
  have hmodulus : 0 < modulus := by simp [modulus]
  have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
  have hdecompose : modulus * quotient + residual = listlen := Nat.div_add_mod listlen modulus
  have htotal : current + listlen = modulus * quotient + (current + residual) := by
    omega
  have hresult : (current + listlen) / modulus =
      quotient + (current + residual) / modulus := by
    rw [htotal, Nat.mul_add_div hmodulus]
  dsimp only [minrunNextSpec]
  rw [hresult]
  by_cases hcarry : current + residual < modulus
  · left
    rw [Nat.div_eq_of_lt hcarry]
    simp [quotient, modulus]
  · right
    have hcarryDiv : (current + residual) / modulus = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hcarryDiv]
    have hremainder : 0 < listlen % modulus := by
      change 0 < residual
      by_contra hzero
      have : residual = 0 := by omega
      omega
    rw [minrunCeilDiv_eq_succ listlen modulus hmodulus hremainder]

/-- Every exact-arithmetic output is either the floor or ceiling target, provided a divisible
list length starts with zero residual. -/
theorem minrunSpecTrace_balanced (calls listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent)
    (hzero : listlen % 2 ^ exponent = 0 → current = 0) :
    ∀ x ∈ (minrunSpecTrace calls listlen exponent current).outputs,
      x = listlen / 2 ^ exponent ∨
        x = minrunCeilDiv listlen (2 ^ exponent) := by
  induction calls generalizing current with
  | zero => simp [minrunSpecTrace]
  | succ calls ih =>
      let next := minrunNextSpec listlen current exponent
      have hnextCurrent : next.residual < 2 ^ exponent := by
        exact Nat.mod_lt _ (pow_pos (by omega) _)
      have hnextZero : listlen % 2 ^ exponent = 0 → next.residual = 0 := by
        intro hdivisible
        have hcurrentZero := hzero hdivisible
        simp [next, minrunNextSpec, hcurrentZero, hdivisible]
      have hhead := minrunNextSpec_balanced listlen exponent current hcurrent
      have htail := ih next.residual hnextCurrent hnextZero
      simp only [minrunSpecTrace, List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · exact hhead
      · exact htail x hx
