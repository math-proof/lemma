module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVandermonde.Part5
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronAnalytic
open Finset Matrix Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexSectorCharacteristicDet
    (N n : Nat) (q : Real × Real) : Real :=
  Matrix.det
    (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) -
      sixVertexSectorTransfer N n q.1)

noncomputable def sixVertexSectorCharacteristicGraph
    (N n : Nat) (q : Real × Real) : Real × Real :=
  (q.1, sixVertexSectorCharacteristicDet N n q)

end
end StatMech.FrontierD
