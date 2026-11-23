/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Hom.PowersetCard
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertex.Part2

@[expose] public section

open Finset Matrix


namespace StatMech.FrontierD

def sixVertexRowDistance {N : ℕ} (x y : SixVertexRow N) : ℕ :=
  #{i | x i ≠ y i}

end StatMech.FrontierD
