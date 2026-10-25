/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part4


namespace StatMech

namespace Exact3D

structure IsingMassRGCoordinateScaffold
    (C : RGCertificate Ising3DModel) where
  
  latticeRG : LatticeRGData 3
  
  scale_match : latticeRG.kernel.scale = C.scale
  

  coordinate : ℝ → C.H.carrier
  
  rgNeighborhood : Set C.H.carrier
  
  renormalizedBeta : ℝ → ℝ
  
  δ : ℝ
  δ_pos : 0 < δ
  
  correlationLength : ℝ → ℝ
  
  mass : ℝ → ℝ
  
  massPrefactor : ℝ → ℝ

end Exact3D
end StatMech
