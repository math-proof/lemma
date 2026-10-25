/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample
open Finset


namespace StatMech.Sharpness

namespace shbK4Edge

instance (e : shbK4Edge) : DecidablePred e.Incident := by
  intro v
  unfold Incident
  split <;> infer_instance

end shbK4Edge
end StatMech.Sharpness
