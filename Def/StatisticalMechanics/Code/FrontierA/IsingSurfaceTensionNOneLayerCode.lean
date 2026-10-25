/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
open Finset


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising


def nOneLayerCodeEquiv : Fin 512 ≃ RectangularLayerConfig 3 3 :=
  (finFunctionFinEquiv (m := 2) (n := 9)).symm |>.trans
    (Equiv.arrowCongr
      (finProdFinEquiv (m := 3) (n := 3)).symm finTwoEquiv)

end StatMech.FrontierA.NOneSymmetricMeanCertificate
