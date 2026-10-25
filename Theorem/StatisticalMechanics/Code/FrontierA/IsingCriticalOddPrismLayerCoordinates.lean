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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

@[simp] theorem oddPrismLowerBlockSiteEquiv_surface
    (n : Nat) (i j : Fin (2 * n + 1)) :
    oddPrismLowerBlockSiteEquiv n (oddPrismLowerHalfSurfaceSite n i j) =
      (i, j, Fin.last n) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      rfl


@[simp] theorem oddPrismUpperBlockReflectedSiteEquiv_surface
    (n : Nat) (hn : 0 < n) (i j : Fin (2 * n + 1)) :
    oddPrismUpperBlockReflectedSiteEquiv n
        (oddPrismUpperHalfSurfaceSite n hn i j) =
      (i, j, oddPrismUpperSeamLayerIndex n hn) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [oddPrismUpperBlockReflectedSiteEquiv,
        oddPrismUpperHalfSurfaceSite, oddPrismUpperSeamLayerIndex]
      omega


theorem spin_oddPrismLowerHalfSurfaceSite_eq_layer
    (n : Nat) (sigma : ConfigSpace (OddPrismLowerBlockSite n))
    (i j : Fin (2 * n + 1)) :
    spin sigma (oddPrismLowerHalfSurfaceSite n i j) =
      spin (oddPrismLowerBlockLayer n sigma (Fin.last n)) (i, j) := by
  unfold oddPrismLowerBlockLayer
  change spin sigma (oddPrismLowerHalfSurfaceSite n i j) =
    spin sigma ((oddPrismLowerBlockSiteEquiv n).symm
      (i, j, Fin.last n))
  have hsite : (oddPrismLowerBlockSiteEquiv n).symm
      (i, j, Fin.last n) = oddPrismLowerHalfSurfaceSite n i j := by
    apply (oddPrismLowerBlockSiteEquiv n).injective
    rw [Equiv.apply_symm_apply]
    exact (oddPrismLowerBlockSiteEquiv_surface n i j).symm
  rw [hsite]


theorem spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer
    (n : Nat) (hn : 0 < n)
    (sigma : ConfigSpace (OddPrismUpperBlockSite n))
    (i j : Fin (2 * n + 1)) :
    spin sigma (oddPrismUpperHalfSurfaceSite n hn i j) =
      spin (oddPrismUpperBlockReflectedLayer n sigma
        (oddPrismUpperSeamLayerIndex n hn))
        (i, j) := by
  unfold oddPrismUpperBlockReflectedLayer
  change spin sigma (oddPrismUpperHalfSurfaceSite n hn i j) =
    spin sigma ((oddPrismUpperBlockReflectedSiteEquiv n).symm
      (i, j, oddPrismUpperSeamLayerIndex n hn))
  have hsite : (oddPrismUpperBlockReflectedSiteEquiv n).symm
      (i, j, oddPrismUpperSeamLayerIndex n hn) =
        oddPrismUpperHalfSurfaceSite n hn i j := by
    apply (oddPrismUpperBlockReflectedSiteEquiv n).injective
    rw [Equiv.apply_symm_apply]
    exact (oddPrismUpperBlockReflectedSiteEquiv_surface n hn i j).symm
  rw [hsite]


theorem oddPrismUnequalBridgeInteraction_eq_layerDotProduct
    (n : Nat) (hn : 0 < n)
    (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n)) :
    unequalReplicaBridgeInteraction
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) a b =
      ∑ p : Fin (2 * n + 1) × Fin (2 * n + 1),
        spin (oddPrismLowerBlockLayer n a (Fin.last n)) p *
          spin (oddPrismUpperBlockReflectedLayer n b
            (oddPrismUpperSeamLayerIndex n hn)) p := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold unequalReplicaBridgeInteraction
  rw [sum_oddPrism_fis_interface n hn]
  apply Finset.sum_congr rfl
  intro p _
  unfold oddPrismCentralInterfaceEdge
  change spin (isingSumConfigEquiv.symm (a, b))
        (Sum.inl (oddPrismLowerHalfSurfaceSite n p.1 p.2)) *
      spin (isingSumConfigEquiv.symm (a, b))
        (Sum.inr (oddPrismUpperHalfSurfaceSite n hn p.1 p.2)) = _
  rw [spin_isingSumConfigEquiv_symm_inl,
    spin_isingSumConfigEquiv_symm_inr]
  rw [spin_oddPrismLowerHalfSurfaceSite_eq_layer,
    spin_oddPrismUpperHalfSurfaceSite_eq_reflectedLayer]


end
end StatMech.FrontierA
