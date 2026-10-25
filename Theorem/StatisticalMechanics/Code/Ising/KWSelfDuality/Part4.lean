/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Def.StatisticalMechanics.Code.Ising.KWSelfDuality.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section SelfDual

open Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


theorem isingZ_self_dual (β βstar c : ℝ)
    (hmatch : DualContourMatching Gp Gd β βstar c) :
    isingZ Gd βstar 0 = c * isingZ Gp β 0 := by
  have hZd := isingZ_high_temp_expansion Gd βstar
  obtain ⟨_, hmatch⟩ := hmatch
  
  rw [hZd, hmatch]


theorem isingZ_self_dual_proportional (β βstar c : ℝ)
    (hmatch : DualContourMatching Gp Gd β βstar c) :
    ∃ factor : ℝ, isingZ Gd βstar 0 = factor * isingZ Gp β 0 :=
  ⟨c, isingZ_self_dual Gp Gd β βstar c hmatch⟩

end SelfDual
end Ising
end StatMech
