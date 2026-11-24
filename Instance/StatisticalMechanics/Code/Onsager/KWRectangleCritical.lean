module
public import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
public import Def.StatisticalMechanics.Code.Onsager.KWRectangleCritical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


instance (M N : Nat) : DecidablePred (ons_rectDartValid M N) :=
  fun d => by
    unfold ons_rectDartValid
    split <;> infer_instance


end StatMech.Onsager
