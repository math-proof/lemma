module
public import Theorem.StatisticalMechanics.Code.FrontierA.FKCriticalAlgebra
public import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
public import Theorem.StatisticalMechanics.Code.Universality.STT.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTrihexDuality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable def fkEdgeOdds (p : ℝ) : ℝ := p / (1 - p)


def triangularFKCriticalSurface (q y0 y1 y2 : ℝ) : ℝ :=
  y0 * y1 * y2 + y0 * y1 + y1 * y2 + y2 * y0 - q


def hexagonalFKCriticalSurface (q y0 y1 y2 : ℝ) : ℝ :=
  y0 * y1 * y2 - q * (y0 + y1 + y2) - q ^ 2


end StatMech.FrontierA
