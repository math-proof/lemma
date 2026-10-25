/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterBridgeCalculus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterBridgeCalculus.Part2
open Finset Filter
open scoped BigOperators


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


theorem replicaBridgeMoment_pos
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    0 < replicaBridgeMoment G J hf sites r := by
  unfold replicaBridgeMoment ghsiExp2
  apply div_pos
  · apply Finset.sum_pos
    · intro a _
      apply Finset.sum_pos
      · intro b _
        exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
          (Real.exp_pos _)
      · exact Finset.univ_nonempty
    · exact Finset.univ_nonempty
  · exact sq_pos_of_pos (ZJ_pos _ _ _)


theorem replicaBridgeMoment_eq_agreementTilt
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMoment G J hf sites r =
      ∑ q : ConfigSpace V, ghsiAgreementProb G J hf q *
        Real.exp (r * replicaAgreementSpin sites q) := by
  unfold replicaBridgeMoment ghsiExp2 ghsiAgreementProb
  rw [ghsL_sum_pair_xnor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  unfold ghsiFibreMass ghsiFibreWeight
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  apply congrArg (fun z => z / ZJ G.edgeFinset J hf ^ 2)
  apply Finset.sum_congr rfl
  intro a ha
  change wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf (ghsLMate q a) *
      Real.exp (r * replicaBridgeInteraction sites a (ghsLMate q a)) = _
  rw [replicaBridgeInteraction_mate]


theorem ghsiExp2_replicaBridgeFunction_eq_agreement
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (F : Real -> Real) :
    ghsiExp2 G J hf (fun a b => F (replicaBridgeInteraction sites a b)) =
      ∑ q : ConfigSpace V, ghsiAgreementProb G J hf q *
        F (replicaAgreementSpin sites q) := by
  unfold ghsiExp2 ghsiAgreementProb
  rw [ghsL_sum_pair_xnor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q hq
  unfold ghsiFibreMass ghsiFibreWeight
  rw [div_mul_eq_mul_div, Finset.sum_mul]
  apply congrArg (fun z => z / ZJ G.edgeFinset J hf ^ 2)
  apply Finset.sum_congr rfl
  intro a ha
  change wJ G.edgeFinset J hf a * wJ G.edgeFinset J hf (ghsLMate q a) *
      F (replicaBridgeInteraction sites a (ghsLMate q a)) = _
  rw [replicaBridgeInteraction_mate]


end
end StatMech.Ising
