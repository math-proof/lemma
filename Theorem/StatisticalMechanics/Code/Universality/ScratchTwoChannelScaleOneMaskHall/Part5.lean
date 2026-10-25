/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Def.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part8


namespace StatMech.Universality

@[simp] theorem rlcScaleOneBoolCubeToBitVec_getLsb
    {n : Nat} (bits : Fin n → Bool) (i : Fin n) :
    (rlcScaleOneBoolCubeToBitVec n bits).getLsb i = bits i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [rlcScaleOneBoolCubeToBitVec]
      · change
          (BitVec.concat (rlcScaleOneBoolCubeToBitVec n (Fin.tail bits))
            (bits 0)).getLsbD (j.val + 1) = bits j.succ
        rw [BitVec.getLsbD_concat_succ]
        simpa [Fin.tail] using ih (Fin.tail bits) j

end StatMech.Universality
