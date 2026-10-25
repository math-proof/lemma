/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Literal.Part2
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

noncomputable def shbK4CurrentEquiv (E : Finset shbK4Edge) :
    (↑E → ℕ) ≃ ((shbK4Graph E).edgeFinset → ℕ) :=
  Equiv.arrowCongr (shbK4GraphEdgeEquiv E) (Equiv.refl ℕ)

end StatMech.Sharpness
