/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part9


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem oddPrismFullSeamInteraction_join
    (n : Nat) (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n)) :
    oddPrismFullSeamInteraction n (oddPrismBlockConfigEquiv n (a, b)) =
      unequalReplicaBridgeInteraction
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) a b := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismFullSeamInteraction
  rw [Equiv.symm_apply_apply]


theorem oddPrismFullSeamInteraction_eq_rectangularInterface
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    oddPrismFullSeamInteraction n sigma =
      rectangularPrismInterfaceInteraction sigma := by
  let p := (oddPrismBlockConfigEquiv n).symm sigma
  have hsigma : oddPrismBlockConfigEquiv n p = sigma :=
    (oddPrismBlockConfigEquiv n).apply_symm_apply sigma
  rw [← hsigma]
  change oddPrismFullSeamInteraction n (oddPrismBlockConfigEquiv n p) = _
  rw [oddPrismFullSeamInteraction_join,
    oddPrismUnequalBridgeInteraction_eq_layerDotProduct n hn]
  unfold rectangularPrismInterfaceInteraction
  rw [dif_pos hn]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro y _
  rw [← spin_oddPrismLowerHalfSurfaceSite_eq_layer,
    ← spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer,
    ← spin_oddPrismBlockConfigEquiv_lower,
    ← spin_oddPrismBlockConfigEquiv_upper]
  rfl


theorem rectangularPrismInterfaceInteraction_eq_layerSeam
    (n : Nat) (hn : 0 < n)
    (sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismInterfaceInteraction sigma =
      oddPrismLayerSeamInteraction n
        (rectangularPrismLayer sigma ⟨n, by omega⟩)
        (rectangularPrismLayer sigma ⟨n + 1, by omega⟩) := by
  unfold rectangularPrismInterfaceInteraction oddPrismLayerSeamInteraction
    rectangularPrismLayer rectangularPrismSpin
  rw [dif_pos hn, Fintype.sum_prod_type]
  rfl


end
end StatMech.FrontierA
