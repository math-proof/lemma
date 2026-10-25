/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode
open Finset


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising


noncomputable def nOneTransferBridgeRawMomentCodeSum (beta r : Real) : Real :=
  ∑ s : Fin 512, ∑ q : Fin 512, ∑ v : Fin 512,
    Real.exp (beta *
        ((layerLateralInt s : Real) + layerDotInt s v +
          layerLateralInt v + layerFaceInt v +
          layerLateralInt q + layerFaceInt q) +
      r * (layerDotInt s q : Real))

end StatMech.FrontierA.NOneSymmetricMeanCertificate
