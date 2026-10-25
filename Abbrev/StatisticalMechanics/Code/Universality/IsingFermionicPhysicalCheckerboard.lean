/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalCheckerboard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCheckerboard


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

abbrev FKIsingSquareRadialPatchDualNode (m : Nat) :=
  {p : Fin m × Fin m // ¬ Even (p.1.1 + p.2.1)}


end
end StatMech.Universality
