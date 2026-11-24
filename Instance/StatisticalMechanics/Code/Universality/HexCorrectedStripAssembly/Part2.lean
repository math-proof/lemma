module
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
public import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part7


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable instance hexCSIncidence_fintype (T L : ℕ) :
    Fintype (HexCSIncidence T L) :=
  Fintype.ofEquiv (HexCSVertex T L × Fin 3) (hexCSIncidenceEquiv T L)

end
end StatMech.Universality
