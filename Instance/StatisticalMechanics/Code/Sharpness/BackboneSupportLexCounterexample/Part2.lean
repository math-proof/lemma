/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part3
open Finset


namespace StatMech.Sharpness

instance (A : Finset shbK4Edge) (p : shbK4Path03) :
    Decidable (shbK4SupportsPath A p) := by
  unfold shbK4SupportsPath
  infer_instance


end StatMech.Sharpness
