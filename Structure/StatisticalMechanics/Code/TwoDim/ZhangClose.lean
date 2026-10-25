/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangLowerBound
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangClose
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace TwoDim

open StatMech.Lattice StatMech.Universality


structure ZhangGeometricData {E : Type*} (μ : Measure (ConfigSpace E))
    (A B : ℕ → Set (ConfigSpace E)) where
  S : Fin 4 → ℕ → Set (ConfigSpace E)
  Err : ℕ → Set (ConfigSpace E)
  Sinc : ∀ i n, IsIncreasing (S i n)
  Sm : ∀ i n, MeasurableSet (S i n)
  Ssym : ∀ i n, μ.real (S i n) = μ.real (S 0 n)
  errTendsto : Tendsto (fun n => μ.real (Err n)) atTop (𝓝 0)
  unionTendsto :
    Tendsto (fun n => μ.real (S 0 n ∪ S 1 n ∪ S 2 n ∪ S 3 n)) atTop (𝓝 1)
  merge : ∀ n, S 0 n ∩ S 1 n ⊆ (A n ∪ B n) ∪ Err n


end TwoDim
end StatMech
