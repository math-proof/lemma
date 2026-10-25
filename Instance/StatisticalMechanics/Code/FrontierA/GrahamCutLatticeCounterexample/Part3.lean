/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part3
open Finset


namespace StatMech.FrontierA

instance grahamC4RootCutSupported_decidable (S : Finset (Fin 4)) :
    Decidable (GrahamC4RootCutSupported S) := by
  unfold GrahamC4RootCutSupported
  infer_instance

end StatMech.FrontierA
