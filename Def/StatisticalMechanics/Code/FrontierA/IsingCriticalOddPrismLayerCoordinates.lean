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


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def oddPrismLowerBlockSiteEquiv (n : Nat) :
    OddPrismLowerBlockSite n ≃
      Fin (2 * n + 1) × Fin (2 * n + 1) × Fin (n + 1) where
  toFun v := (v.1.x, v.1.y, ⟨v.1.z.val, by
    have hz := v.2
    unfold oddPrismAtOrBelowCenter at hz
    omega⟩)
  invFun p := ⟨⟨p.1, p.2.1, ⟨p.2.2.val, by omega⟩⟩, by
    unfold oddPrismAtOrBelowCenter
    have hz := p.2.2.isLt
    change p.2.2.val <= n
    omega⟩
  left_inv v := by
    apply Subtype.ext
    cases v.1
    rfl
  right_inv p := by
    rcases p with ⟨x, y, z⟩
    rfl


def oddPrismUpperBlockReflectedSiteEquiv (n : Nat) :
    OddPrismUpperBlockSite n ≃
      Fin (2 * n + 1) × Fin (2 * n + 1) × Fin n where
  toFun v := (v.1.x, v.1.y, ⟨2 * n - v.1.z.val, by
    have hzUpper := v.2
    have hzLt := v.1.z.isLt
    unfold oddPrismAtOrBelowCenter at hzUpper
    omega⟩)
  invFun p := ⟨⟨p.1, p.2.1, ⟨2 * n - p.2.2.val, by
    have hk := p.2.2.isLt
    omega⟩⟩, by
    have hk := p.2.2.isLt
    unfold oddPrismAtOrBelowCenter
    change ¬2 * n - p.2.2.val <= n
    omega⟩
  left_inv v := by
    apply Subtype.ext
    cases v with
    | mk v hv =>
      cases v with
      | mk x y z =>
        have hzLt := z.isLt
        simp only
        congr
        omega
  right_inv p := by
    rcases p with ⟨x, y, k⟩
    have hk := k.isLt
    simp only
    congr
    omega


def oddPrismLowerBlockLayer (n : Nat)
    (sigma : ConfigSpace (OddPrismLowerBlockSite n)) (k : Fin (n + 1)) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) :=
  fun p => sigma ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))


def oddPrismUpperBlockReflectedLayer (n : Nat)
    (sigma : ConfigSpace (OddPrismUpperBlockSite n)) (k : Fin n) :
    RectangularLayerConfig (2 * n + 1) (2 * n + 1) :=
  fun p => sigma
    ((oddPrismUpperBlockReflectedSiteEquiv n).symm (p.1, p.2, k))


def oddPrismLowerBlockLayerEquiv (n : Nat) :
    ConfigSpace (OddPrismLowerBlockSite n) ≃
      (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) where
  toFun := oddPrismLowerBlockLayer n
  invFun q := fun v =>
    q (oddPrismLowerBlockSiteEquiv n v).2.2
      ((oddPrismLowerBlockSiteEquiv n v).1,
        (oddPrismLowerBlockSiteEquiv n v).2.1)
  left_inv sigma := by
    funext v
    change sigma ((oddPrismLowerBlockSiteEquiv n).symm
      (oddPrismLowerBlockSiteEquiv n v)) = sigma v
    rw [Equiv.symm_apply_apply]
  right_inv q := by
    funext k p
    change q
        (oddPrismLowerBlockSiteEquiv n
          ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))).2.2
        ((oddPrismLowerBlockSiteEquiv n
          ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))).1,
          (oddPrismLowerBlockSiteEquiv n
            ((oddPrismLowerBlockSiteEquiv n).symm (p.1, p.2, k))).2.1) =
      q k p
    rw [Equiv.apply_symm_apply]


def oddPrismUpperBlockReflectedLayerEquiv (n : Nat) :
    ConfigSpace (OddPrismUpperBlockSite n) ≃
      (Fin n -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) where
  toFun := oddPrismUpperBlockReflectedLayer n
  invFun q := fun v =>
    q (oddPrismUpperBlockReflectedSiteEquiv n v).2.2
      ((oddPrismUpperBlockReflectedSiteEquiv n v).1,
        (oddPrismUpperBlockReflectedSiteEquiv n v).2.1)
  left_inv sigma := by
    funext v
    change sigma ((oddPrismUpperBlockReflectedSiteEquiv n).symm
      (oddPrismUpperBlockReflectedSiteEquiv n v)) = sigma v
    rw [Equiv.symm_apply_apply]
  right_inv q := by
    funext k p
    change q
        (oddPrismUpperBlockReflectedSiteEquiv n
          ((oddPrismUpperBlockReflectedSiteEquiv n).symm
            (p.1, p.2, k))).2.2
        ((oddPrismUpperBlockReflectedSiteEquiv n
          ((oddPrismUpperBlockReflectedSiteEquiv n).symm
            (p.1, p.2, k))).1,
          (oddPrismUpperBlockReflectedSiteEquiv n
            ((oddPrismUpperBlockReflectedSiteEquiv n).symm
              (p.1, p.2, k))).2.1) = q k p
    rw [Equiv.apply_symm_apply]


def oddPrismUpperSeamLayerIndex (n : Nat) (hn : 0 < n) : Fin n :=
  ⟨n - 1, by omega⟩


end
end StatMech.FrontierA
