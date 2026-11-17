/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Onsager.Torus
open SimpleGraph


namespace StatMech.BeffaraDC

open StatMech.Onsager


public inductive TorusEdgeOrientation
  | horizontal
  | vertical
  deriving DecidableEq


end StatMech.BeffaraDC
