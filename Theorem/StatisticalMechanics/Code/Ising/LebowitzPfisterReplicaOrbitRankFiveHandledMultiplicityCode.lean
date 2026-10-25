/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part7
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledMultiplicityCode


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem finiteFiberMultiplicityCode_key_injective
    {S T : Type*} [Fintype S] [Fintype T]
    (key : S -> T)
    (hfiber : forall target, Fintype.card {s : S // key s = target} <= 2) :
    Function.Injective
      (fun s => (finiteFiberMultiplicityCode key hfiber s, key s)) := by
  intro s t hst
  have hkey : key s = key t := congrArg Prod.snd hst
  have hbit : finiteFiberMultiplicityCode key hfiber s =
      finiteFiberMultiplicityCode key hfiber t := congrArg Prod.fst hst
  unfold finiteFiberMultiplicityCode at hbit
  cases hkey
  exact congrArg Subtype.val
    ((finiteFiberMultiplicityEmbedding key hfiber (key s)).injective hbit)


end
end StatMech.Ising
