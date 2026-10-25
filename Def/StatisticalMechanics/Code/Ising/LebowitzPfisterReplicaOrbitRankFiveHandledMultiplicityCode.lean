/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part7


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def finiteFiberMultiplicityEmbedding
    {S T : Type*} [Fintype S] [Fintype T]
    (key : S -> T)
    (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2)
    (target : T) : {s : S // key s = target} ↪ Fin 2 := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa using hfiber target


noncomputable def finiteFiberMultiplicityCode
    {S T : Type*} [Fintype S] [Fintype T]
    (key : S -> T)
    (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2)
    (s : S) : Fin 2 :=
  finiteFiberMultiplicityEmbedding key hfiber (key s) ⟨s, rfl⟩


end
end StatMech.Ising
