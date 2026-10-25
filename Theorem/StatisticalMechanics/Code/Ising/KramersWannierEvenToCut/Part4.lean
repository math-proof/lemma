/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


omit [Fintype V] [DecidableRel Gp.Adj] in


theorem mem_image_symm_iff (ψ : Sym2 V ≃ Sym2 V) (F : Finset (Sym2 V)) (e : Sym2 V) :
    e ∈ F.image ψ.symm ↔ ψ e ∈ F := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩; rwa [Equiv.apply_symm_apply]
  · intro he; exact ⟨ψ e, he, ψ.symm_apply_apply e⟩

omit [Fintype V] [DecidableRel Gp.Adj] in


theorem walkParity_image_symm (ψ : Sym2 V ≃ Sym2 V) (F : Finset (Sym2 V))
    {x y : V} (p : Gp.Walk x y) :
    walkParity Gp (F.image ψ.symm) p
      = (p.darts.map (fun d => decide (ψ s(d.fst, d.snd) ∈ F))).foldr Bool.xor false := by
  induction p with
  | nil => simp [walkParity]
  | @cons u v w h q ih =>
    rw [walkParity_cons, ih, SimpleGraph.Walk.darts_cons]
    simp only [List.map_cons, List.foldr_cons]
    congr 1
    rw [decide_eq_decide]
    exact mem_image_symm_iff ψ F s(u, v)


theorem image_symm_subset_edgeFinset (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    {F : Finset (Sym2 V)} (hF : F ⊆ Gd.edgeFinset) :
    F.image ψ.symm ⊆ Gp.edgeFinset := by
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨g, hg, rfl⟩ := he
  exact hsymm g (hF hg)


theorem even_to_cut_of_cycleParity [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hcyc : ∀ F ∈ evenSubgraphs Gd, CycleParityCompatible Gp ψ F) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp := by
  intro F hF
  have hFsub : F ⊆ Gd.edgeFinset := by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hF
    exact hF.1
  exact mem_cutSpace_of_evenOnCycles hG
    (image_symm_subset_edgeFinset ψ hsymm hFsub) (hcyc F hF)


end Reduction
end Ising
end StatMech
