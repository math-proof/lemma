/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part4


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

instance (b0 b1 b2 b3 : Fin 2) (y : Fin 3 → Fin 2) :
    Decidable (ons_decChainEven b0 b1 b2 b3 y) := by
  unfold ons_decChainEven
  infer_instance


end StatMech.Onsager
