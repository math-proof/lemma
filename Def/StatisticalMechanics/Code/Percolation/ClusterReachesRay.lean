/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


def crr_ClusterRunsAlongAxis (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) :
    Prop :=
  ∃ L : ℕ,
    (∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) ∧
    Connected d ω x (hrHD_rayPt j 1) ∧
    Connected d (removeSite 0 ω) x (hrHD_rayPt j 1) ∧
    (cluster d (removeSite 0 ω) x).Infinite


end Percolation
end StatMech
