/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKTwoPointQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.FreeWiredAgreeClose.Part3
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Theorem.StatisticalMechanics.Code.Exact3D.FKTwoPointQ2Bridge.Part3
open Filter
open MeasureTheory


namespace StatMech

namespace Exact3D

open FK


def FreeFiniteVolumeQ2ExactExponentialOfBeta
    (β : ℝ) (hβpos : 0 < β) (A mass : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ M in atTop,
    (freeFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (boxConnEvent 3 n (ising3DOriginBoxVertex n)
          (ising3DXAxisBoxVertex n)) =
      A * Real.exp (-(mass * (n : ℝ)))


def WiredFiniteVolumeQ2ExactExponentialOfBeta
    (β : ℝ) (hβpos : 0 < β) (A mass : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ᶠ M in atTop,
    (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
      (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (boxConnEvent 3 n (ising3DOriginBoxVertex n)
          (ising3DXAxisBoxVertex n)) =
      A * Real.exp (-(mass * (n : ℝ)))


def FreeFiniteVolumeQ2SubexponentialPrefactorOfBeta
    (β : ℝ) (hβpos : 0 < β) (A : ℕ → ℝ) (mass : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < A n) ∧
    Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
      atTop (nhds 0) ∧
    ∀ᶠ n in atTop, ∀ᶠ M in atTop,
      (freeFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxConnEvent 3 n (ising3DOriginBoxVertex n)
            (ising3DXAxisBoxVertex n)) =
        A n * Real.exp (-(mass * (n : ℝ)))


def WiredFiniteVolumeQ2SubexponentialPrefactorOfBeta
    (β : ℝ) (hβpos : 0 < β) (A : ℕ → ℝ) (mass : ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < A n) ∧
    Tendsto (fun n : ℕ => Real.log (A n) / (n : ℝ))
      atTop (nhds 0) ∧
    ∀ᶠ n in atTop, ∀ᶠ M in atTop,
      (wiredFiniteMeasure 3 M (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (boxConnEvent 3 n (ising3DOriginBoxVertex n)
            (ising3DXAxisBoxVertex n)) =
        A n * Real.exp (-(mass * (n : ℝ)))


end Exact3D
end StatMech
