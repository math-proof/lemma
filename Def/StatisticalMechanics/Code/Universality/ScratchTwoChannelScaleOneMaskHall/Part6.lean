/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelScaleOneMaskHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelDynamicEdgeEncoding.Part3
import Theorem.StatisticalMechanics.Code.Universality.ScratchTwoChannelScaleOneMaskHall.Part3


namespace StatMech.Universality

noncomputable def rlcScaleOnePairBlockEquivFin :
    Equiv RlcScaleOnePairBlockFailure (Fin 3) :=
  Fintype.equivFinOfCardEq rlcScaleOnePairBlockFailure_card

noncomputable def rlcScaleOneFiveBlockEquivFin :
    Equiv RlcScaleOneFiveBlockFailure (Fin 25) :=
  Fintype.equivFinOfCardEq rlcScaleOneFiveBlockFailure_card

noncomputable def rlcScaleOneUnusedBlockEquivFin :
    Equiv RlcScaleOneUnusedBlock (Fin 8) :=
  Fintype.equivFinOfCardEq (by
    simp only [RlcScaleOneUnusedBlock, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool]
    norm_num)

noncomputable def rlcScaleOneSectionAFactorsEquivFin :
    Equiv RlcScaleOneSectionAFactors (Fin 15000) :=
  (Equiv.prodCongr rlcScaleOnePairBlockEquivFin
    (Equiv.prodCongr rlcScaleOneFiveBlockEquivFin
      (Equiv.prodCongr rlcScaleOneFiveBlockEquivFin
        rlcScaleOneUnusedBlockEquivFin))).trans
    ((Equiv.prodCongr (Equiv.refl (Fin 3))
      ((Equiv.prodCongr (Equiv.refl (Fin 25)) finProdFinEquiv).trans
        finProdFinEquiv)).trans finProdFinEquiv)

noncomputable def rlcScaleOneSectionAEncoder :
    RlcScaleOneSectionAFailure ↪ Fin (2 ^ 14) :=
  (rlcScaleOneSectionAFactorEquiv.trans
    rlcScaleOneSectionAFactorsEquivFin).toEmbedding.trans
      (Fin.castLEEmb (by norm_num))

noncomputable def rlcScaleOneSectionBEncoder :
    RlcScaleOneSectionBFailure ↪ Fin (2 ^ 12) :=
  rlcScaleOneSectionBListEquiv.symm.toEmbedding |>.trans
    (Fin.castLEEmb (by rw [rlcScaleOneSectionBList_length]; norm_num))

noncomputable def rlcScaleOneSectionCEncoder :
    RlcScaleOneSectionCFailure ↪ Fin (2 ^ 11) :=
  rlcScaleOneSectionCListEquiv.symm.toEmbedding |>.trans
    (Fin.castLEEmb (by rw [rlcScaleOneSectionCList_length]; norm_num))

end StatMech.Universality
