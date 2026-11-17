/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/GroundUpWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Structure.StatisticalMechanics.Code.Onsager.GroundUpWinding

@[expose] public section

namespace StatMech.Onsager.GroundUp

def RectPolygonData.balance (D : RectPolygonData) (P : D.Poly) : ℤ := D.cc P - D.rc P


end StatMech.Onsager.GroundUp
