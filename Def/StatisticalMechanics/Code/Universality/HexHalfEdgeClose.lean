module
public import Theorem.StatisticalMechanics.Code.Universality.HexW2Weight.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexPerScaleBijClose.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open HexWalk List

open scoped BigOperators


noncomputable def hhe_rho (h h' : ℤ) : ℂ := hexUnit h' * (hexUnit h)⁻¹


end StatMech.Universality
