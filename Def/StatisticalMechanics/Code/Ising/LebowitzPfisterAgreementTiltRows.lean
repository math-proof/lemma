/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterAgreementTiltRows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterAgreementTiltFKG
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
open Finset
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness StatMech.Walls.VBG

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


noncomputable def replicaAgreementTiltCovarianceRow
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (i : I) (r : Real) : Real :=
  vbg_cov (replicaAgreementTiltProb G J hf sites r)
    (fun q => spin q (sites i)) (replicaAgreementSpin sites)


end
end StatMech.Ising
