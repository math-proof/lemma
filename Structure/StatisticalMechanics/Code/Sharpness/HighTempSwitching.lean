/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part2
open Finset
open scoped symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


structure HighTempFirstExit (K : Finset (Sym2 V)) (o z : V)
    (S : Finset V) where
  x : V
  y : V
  Q : Finset (Sym2 V)
  x_mem : x ∈ S
  y_notMem : y ∉ S
  Q_subset : Q ⊆ K
  Q_inside : ∀ e ∈ Q, edgeInside S e
  Q_sources : HasOddBoundary Q (sourcePair o x)
  exit_mem : s(x, y) ∈ K
  exit_notMem : s(x, y) ∉ Q
  ne : x ≠ y


end Sharpness
end StatMech
