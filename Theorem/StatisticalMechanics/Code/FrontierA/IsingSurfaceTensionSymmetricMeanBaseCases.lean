/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalSymmetricMean.Part2


namespace StatMech.FrontierA

open StatMech StatMech.Ising

noncomputable section

theorem fis_interface_eq_empty_of_right_empty
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K) :
    StatMech.FK.fis_interface G H K = ∅ := by
  classical
  ext e
  constructor
  · intro he
    exfalso
    rw [StatMech.FK.fis_interface, Finset.mem_sdiff,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset] at he
    obtain ⟨hK, hnot⟩ := he
    induction e using Sym2.ind with
    | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at hK hnot
        match x, y with
        | Sum.inl a, Sum.inl b => exact hnot (hcross.inl a b hK)
        | Sum.inl _, Sum.inr b => exact isEmptyElim b
        | Sum.inr a, _ => exact isEmptyElim a
  · simp


theorem unequalReplicaBridgeInteraction_eq_zero_of_right_empty
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (a : ConfigSpace V) (b : ConfigSpace W) :
    unequalReplicaBridgeInteraction G H K a b = 0 := by
  rw [unequalReplicaBridgeInteraction,
    fis_interface_eq_empty_of_right_empty G H K hcross]
  simp


theorem unequalReplicaBridgeMean_eq_zero_of_right_empty
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeMean G H K J hf hg r = 0 := by
  have hinteraction (a : ConfigSpace V) (b : ConfigSpace W) :
      unequalReplicaBridgeInteraction G H K a b = 0 :=
    unequalReplicaBridgeInteraction_eq_zero_of_right_empty
      G H K hcross a b
  simp [unequalReplicaBridgeMean, hinteraction]


end
end StatMech.FrontierA
