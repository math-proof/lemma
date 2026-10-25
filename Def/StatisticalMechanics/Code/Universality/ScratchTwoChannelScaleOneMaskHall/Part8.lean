/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part4


namespace StatMech.Universality

def rlcScaleOneFiberARestrict :
    RlcScaleOneFiberA ↪ RlcScaleOneSectionAFailure where
  toFun omega := ⟨rlcScaleOneRestrictA omega.1, omega.2.2⟩
  inj' omega omega' h := by
    apply Subtype.ext
    have hfun : rlcScaleOneRestrictA omega.1 =
        rlcScaleOneRestrictA omega'.1 := congrArg Subtype.val h
    have h6 := rlcScaleOneRouteClass_zero_fixed omega.1 omega.2.1
    have h6' := rlcScaleOneRouteClass_zero_fixed omega'.1 omega'.2.1
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictA]

def rlcScaleOneFiberBRestrict :
    RlcScaleOneFiberB ↪ RlcScaleOneSectionBFailure where
  toFun omega := ⟨rlcScaleOneRestrictB omega.1, omega.2.2⟩
  inj' omega omega' h := by
    apply Subtype.ext
    have hfun : rlcScaleOneRestrictB omega.1 =
        rlcScaleOneRestrictB omega'.1 := congrArg Subtype.val h
    have hfix := rlcScaleOneRouteClass_one_fixed omega.1 omega.2.1
    have hfix' := rlcScaleOneRouteClass_one_fixed omega'.1 omega'.2.1
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictB]

def rlcScaleOneFiberCRestrict :
    RlcScaleOneFiberC ↪ RlcScaleOneSectionCFailure where
  toFun omega := ⟨rlcScaleOneRestrictC omega.1, omega.2.2⟩
  inj' omega omega' h := by
    apply Subtype.ext
    have hfun : rlcScaleOneRestrictC omega.1 =
        rlcScaleOneRestrictC omega'.1 := congrArg Subtype.val h
    have hfix := rlcScaleOneRouteClass_two_fixed omega.1 omega.2.1
    have hfix' := rlcScaleOneRouteClass_two_fixed omega'.1 omega'.2.1
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictC]

def rlcScaleOneFiberDRestrict :
    RlcScaleOneFiberD ↪ (Fin 12 → Bool) where
  toFun omega := rlcScaleOneRestrictD omega.1
  inj' omega omega' h := by
    apply Subtype.ext
    have h2 := omega.2.2.1
    have h5 := omega.2.2.2.1
    have h6 := omega.2.2.2.2.1
    have h8 := omega.2.2.2.2.2
    have h2' := omega'.2.2.1
    have h5' := omega'.2.2.2.1
    have h6' := omega'.2.2.2.2.1
    have h8' := omega'.2.2.2.2.2
    funext i
    fin_cases i <;> simp_all [rlcScaleOneRestrictD]

def rlcScaleOneBoolCubeToBitVec : (n : Nat) → (Fin n → Bool) → BitVec n
  | 0, _ => BitVec.nil
  | n + 1, bits =>
      BitVec.concat (rlcScaleOneBoolCubeToBitVec n (Fin.tail bits)) (bits 0)

end StatMech.Universality
