/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3


namespace StatMech.Universality

open Finset

noncomputable section

abbrev IsingLeapfrogBox (R : Nat) := Fin (R + 1) × Fin (R + 1)

end
end StatMech.Universality
