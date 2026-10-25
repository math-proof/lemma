/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part5


namespace StatMech.Universality

def rlcScaleOneFinPowTwoEquivBoolCube (n : Nat) :
    Equiv (Fin (2 ^ n)) (Fin n → Bool) :=
  BitVec.equivFin.symm.toEquiv.trans
    { toFun := fun bits => bits.getLsb
      invFun := rlcScaleOneBoolCubeToBitVec n
      left_inv := fun bits => by
        apply BitVec.eq_of_getElem_eq
        intro i hi
        simpa using rlcScaleOneBoolCubeToBitVec_getLsb
          (fun j : Fin n => bits.getLsb j) ⟨i, hi⟩
      right_inv := fun bits => by
        funext i
        exact rlcScaleOneBoolCubeToBitVec_getLsb bits i }

noncomputable def rlcScaleOneFiberAPayload :
    RlcScaleOneFiberA ↪ (Fin 14 → Bool) :=
  (rlcScaleOneFiberARestrict.trans rlcScaleOneSectionAEncoder).trans
    (rlcScaleOneFinPowTwoEquivBoolCube 14).toEmbedding

noncomputable def rlcScaleOneFiberBPayload :
    RlcScaleOneFiberB ↪ (Fin 12 → Bool) :=
  (rlcScaleOneFiberBRestrict.trans rlcScaleOneSectionBEncoder).trans
    (rlcScaleOneFinPowTwoEquivBoolCube 12).toEmbedding

noncomputable def rlcScaleOneFiberCPayload :
    RlcScaleOneFiberC ↪ (Fin 11 → Bool) :=
  (rlcScaleOneFiberCRestrict.trans rlcScaleOneSectionCEncoder).trans
    (rlcScaleOneFinPowTwoEquivBoolCube 11).toEmbedding

def rlcScaleOneCodeA (payload : Fin 14 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, payload 2, payload 3, payload 4, payload 5,
    payload 6, true, true, payload 7, payload 8, payload 9,
    payload 10, payload 11, payload 12, payload 13]

def rlcScaleOneCodeB (payload : Fin 12 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, true, payload 2, payload 3, payload 4,
    true, true, false, payload 5, payload 6, payload 7,
    payload 8, payload 9, payload 10, payload 11]

def rlcScaleOneCodeC (payload : Fin 11 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, false, payload 2, payload 3, true,
    true, true, false, payload 4, payload 5, payload 6,
    payload 7, payload 8, payload 9, payload 10]

def rlcScaleOneCodeD (payload : Fin 12 → Bool) : RlcScaleOneEdgeConfig :=
  ![payload 0, payload 1, payload 2, payload 3, payload 4, payload 5,
    payload 6, false, payload 7, payload 8, true, true,
    true, payload 9, payload 10, payload 11]

def rlcScaleOneCodeAEmbedding :
    (Fin 14 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeA
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeA]

def rlcScaleOneCodeBEmbedding :
    (Fin 12 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeB
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeB]

def rlcScaleOneCodeCEmbedding :
    (Fin 11 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeC
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeC]

def rlcScaleOneCodeDEmbedding :
    (Fin 12 → Bool) ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneCodeD
  inj' payload payload' h := by
    funext i
    fin_cases i <;> simp_all [rlcScaleOneCodeD]

noncomputable def rlcScaleOneFiberATarget :
    RlcScaleOneFiberA ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberAPayload.trans rlcScaleOneCodeAEmbedding

noncomputable def rlcScaleOneFiberBTarget :
    RlcScaleOneFiberB ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberBPayload.trans rlcScaleOneCodeBEmbedding

noncomputable def rlcScaleOneFiberCTarget :
    RlcScaleOneFiberC ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberCPayload.trans rlcScaleOneCodeCEmbedding

def rlcScaleOneFiberDTarget :
    RlcScaleOneFiberD ↪ RlcScaleOneEdgeConfig :=
  rlcScaleOneFiberDRestrict.trans rlcScaleOneCodeDEmbedding

end StatMech.Universality
