/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianContinuousModification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
import Def.StatisticalMechanics.Code.SLE.BrownianContinuousModification.Part2
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

theorem brownianContinuousModification_eq_dyadicLimit
    (omega : Real -> Real) (N : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N) :
    brownianContinuousModification t omega = brownianDyadicLimit N t omega := by
  have hRadius : brownianCompactRadius t <= N := by
    unfold brownianCompactRadius
    exact Nat.ceil_le.mpr (abs_le.mpr ⟨htLower, htUpper⟩)
  change brownianDyadicLimit (brownianCompactRadius t) t omega =
    brownianDyadicLimit N t omega
  exact (brownianDyadicLimit_eq_of_le omega (brownianCompactRadius t) N hRadius
    (neg_brownianCompactRadius_le t)).symm


theorem continuous_brownianContinuousModification
    (omega : Real -> Real)
    (hgood : ∀ N : Nat, ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    Continuous (fun t => brownianContinuousModification t omega) := by
  rw [continuous_iff_continuousAt]
  intro t
  let N : Nat := brownianCompactRadius t + 1
  have htLower : -(N : Real) < t := by
    have h := neg_brownianCompactRadius_le t
    dsimp only [N]
    push_cast
    linarith
  have htUpper : t < N := by
    have h := le_brownianCompactRadius t
    dsimp only [N]
    push_cast
    linarith
  have hfixed : ContinuousAt (fun s => brownianDyadicLimit N s omega) t :=
    ((continuousOn_brownianDyadicLimit omega N (hgood N))
      t ⟨htLower.le, htUpper.le⟩).continuousAt (Icc_mem_nhds htLower htUpper)
  apply hfixed.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds htLower htUpper] with s hs
  exact brownianContinuousModification_eq_dyadicLimit omega N hs.1 hs.2

end StatMech.SLE
