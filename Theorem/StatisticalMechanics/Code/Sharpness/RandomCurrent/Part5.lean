/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part4
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


@[refl]
theorem CurrentConnected.refl (n : Current V) (x : V) : CurrentConnected G n x x :=
  SimpleGraph.Reachable.refl x

theorem CurrentConnected.symm {n : Current V} {x y : V}
    (h : CurrentConnected G n x y) : CurrentConnected G n y x :=
  SimpleGraph.Reachable.symm h

theorem CurrentConnected.trans {n : Current V} {x y z : V}
    (hxy : CurrentConnected G n x y) (hyz : CurrentConnected G n y z) :
    CurrentConnected G n x z :=
  SimpleGraph.Reachable.trans hxy hyz


end Sharpness
end StatMech
