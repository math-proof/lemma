/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierC.IsingTransfer.Part5
open Matrix Polynomial


namespace StatMech.FrontierB

open StatMech.FrontierC

noncomputable def isingTransferProjectorPlus (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (isingTransferEigenPlus beta h - isingTransferEigenMinus beta h)⁻¹ •
    (isingTransferReal beta h - isingTransferEigenMinus beta h • 1)

noncomputable def isingTransferProjectorMinus (beta h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (isingTransferEigenPlus beta h - isingTransferEigenMinus beta h)⁻¹ •
    (isingTransferEigenPlus beta h • 1 - isingTransferReal beta h)

end StatMech.FrontierB
