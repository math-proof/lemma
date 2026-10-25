/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
import Structure.CPythonListsort.Code.Equivalence.MinrunResults
/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

/-- One adaptive-minrun call passes its assertion, returns a target in the
public `1 .. MAX_MINRUN` band, and preserves the bounded-current fact. -/
theorem minrunNext_range (state : MinrunState)
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

theorem MinrunRangeInv.next
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
theorem minrunNextN_range
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

end CPythonListsort
