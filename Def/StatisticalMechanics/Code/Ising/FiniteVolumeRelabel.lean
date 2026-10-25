/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
open Finset


namespace StatMech

namespace Ising

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


def isingCfgEquiv (σ : V ≃ W) : ConfigSpace W ≃ ConfigSpace V where
  toFun ω := fun x => ω (σ x)
  invFun ω := fun y => ω (σ.symm y)
  left_inv ω := by funext y; simp
  right_inv ω := by funext x; simp

end Ising
end StatMech
