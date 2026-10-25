/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Abbrev.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part6


namespace StatMech.Universality

noncomputable def rlcScaleOneTaggedTarget
    (rho : RlcScaleOneRoutedFailure) : RlcScaleOneEdgeConfig :=
  match rho with
  | Sum.inl a => rlcScaleOneFiberATarget a
  | Sum.inr (Sum.inl b) => rlcScaleOneFiberBTarget b
  | Sum.inr (Sum.inr (Sum.inl c)) => rlcScaleOneFiberCTarget c
  | Sum.inr (Sum.inr (Sum.inr d)) => rlcScaleOneFiberDTarget d

noncomputable def rlcScaleOneTaggedTargetEmbedding :
    RlcScaleOneRoutedFailure ↪ RlcScaleOneEdgeConfig where
  toFun := rlcScaleOneTaggedTarget
  inj' rho rho' h := by
    rcases rho with a | bcd
    · rcases rho' with a' | bcd'
      · exact congrArg Sum.inl (rlcScaleOneFiberATarget.injective h)
      · rcases bcd' with b' | cd'
        · exact (rlcScaleOneCodeA_ne_codeB
            (rlcScaleOneFiberAPayload a)
            (rlcScaleOneFiberBPayload b') h).elim
        · rcases cd' with c' | d'
          · exact (rlcScaleOneCodeA_ne_codeC
              (rlcScaleOneFiberAPayload a)
              (rlcScaleOneFiberCPayload c') h).elim
          · exact (rlcScaleOneCodeA_ne_codeD
              (rlcScaleOneFiberAPayload a)
              (rlcScaleOneFiberDRestrict d') h).elim
    · rcases bcd with b | cd
      · rcases rho' with a' | bcd'
        · exact (rlcScaleOneCodeA_ne_codeB
            (rlcScaleOneFiberAPayload a')
            (rlcScaleOneFiberBPayload b) h.symm).elim
        · rcases bcd' with b' | cd'
          · exact congrArg (fun z => Sum.inr (Sum.inl z))
              (rlcScaleOneFiberBTarget.injective h)
          · rcases cd' with c' | d'
            · exact (rlcScaleOneCodeB_ne_codeC
                (rlcScaleOneFiberBPayload b)
                (rlcScaleOneFiberCPayload c') h).elim
            · exact (rlcScaleOneCodeB_ne_codeD
                (rlcScaleOneFiberBPayload b)
                (rlcScaleOneFiberDRestrict d') h).elim
      · rcases cd with c | d
        · rcases rho' with a' | bcd'
          · exact (rlcScaleOneCodeA_ne_codeC
              (rlcScaleOneFiberAPayload a')
              (rlcScaleOneFiberCPayload c) h.symm).elim
          · rcases bcd' with b' | cd'
            · exact (rlcScaleOneCodeB_ne_codeC
                (rlcScaleOneFiberBPayload b')
                (rlcScaleOneFiberCPayload c) h.symm).elim
            · rcases cd' with c' | d'
              · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z)))
                  (rlcScaleOneFiberCTarget.injective h)
              · exact (rlcScaleOneCodeC_ne_codeD
                  (rlcScaleOneFiberCPayload c)
                  (rlcScaleOneFiberDRestrict d') h).elim
        · rcases rho' with a' | bcd'
          · exact (rlcScaleOneCodeA_ne_codeD
              (rlcScaleOneFiberAPayload a')
              (rlcScaleOneFiberDRestrict d) h.symm).elim
          · rcases bcd' with b' | cd'
            · exact (rlcScaleOneCodeB_ne_codeD
                (rlcScaleOneFiberBPayload b')
                (rlcScaleOneFiberDRestrict d) h.symm).elim
            · rcases cd' with c' | d'
              · exact (rlcScaleOneCodeC_ne_codeD
                  (rlcScaleOneFiberCPayload c')
                  (rlcScaleOneFiberDRestrict d) h.symm).elim
              · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr z)))
                  (rlcScaleOneFiberDTarget.injective h)

def rlcScaleOneFourRouteSuccess (eta : RlcScaleOneEdgeConfig) : Bool :=
  (eta 7 && eta 8) || (eta 2 && eta 6 && eta 7) ||
    (eta 5 && eta 6 && eta 7) || (eta 10 && eta 11 && eta 12)

end StatMech.Universality
