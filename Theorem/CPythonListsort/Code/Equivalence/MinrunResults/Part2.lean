/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Equivalence/MinrunResults.lean -/

import Def.CPythonListsort.Code.Equivalence.Minrun.Part2
import Def.CPythonListsort.Code.Equivalence.PowerloopResults.Part2
import Mathlib
import Def.CPythonListsort.Code.Equivalence.MinrunResults
/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/


namespace CPythonListsort

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

end CPythonListsort
