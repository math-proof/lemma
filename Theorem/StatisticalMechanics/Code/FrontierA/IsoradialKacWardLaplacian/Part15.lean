/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part16


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


omit [Fintype V] [DecidableEq V] in
theorem isoradialMuConductance_eq_I_mul
    (theta : V -> V -> Real) :
    isoradialMuConductance theta =
      fun v w => Complex.I * isoradialLaplacianConductance theta v w := by
  funext v w
  rfl


theorem finiteTwistedLaplacian_isoradialMu
    (theta : V -> V -> Real) (transport : V -> V -> Complex) :
    finiteTwistedLaplacian (isoradialMuConductance theta) transport =
      Complex.I • finiteTwistedLaplacian
        (isoradialLaplacianConductance theta) transport := by
  rw [isoradialMuConductance_eq_I_mul,
    finiteTwistedLaplacian_const_mul]


theorem det_finiteTwistedLaplacian_isoradialMu
    (theta : V -> V -> Real) (transport : V -> V -> Complex) :
    (finiteTwistedLaplacian (isoradialMuConductance theta) transport).det =
      Complex.I ^ Fintype.card V *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance theta) transport).det := by
  rw [finiteTwistedLaplacian_isoradialMu, Matrix.det_smul]


end StatMech.FrontierA
