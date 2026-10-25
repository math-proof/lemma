/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Inductive.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample
open Finset


namespace StatMech.Sharpness

namespace shbK4Edge

def Incident : shbK4Edge → Fin 4 → Prop
  | e01, v => v = 0 ∨ v = 1
  | e02, v => v = 0 ∨ v = 2
  | e03, v => v = 0 ∨ v = 3
  | e12, v => v = 1 ∨ v = 2
  | e13, v => v = 1 ∨ v = 3
  | e23, v => v = 2 ∨ v = 3

end shbK4Edge
end StatMech.Sharpness
