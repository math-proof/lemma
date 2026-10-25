/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bof2leafcount.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgf2faithcontract.Part5
import Def.StatisticalMechanics.Code.Walls.bfctfinitecount.Part4
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

theorem bfct_star_cut : ¬ (bkg_deleteVertex bfct_star (0 : Fin 4)).Reachable 1 2 := by
  have hiso : ∀ z, ¬ (bkg_deleteVertex bfct_star 0).Adj 1 z := by decide
  intro h
  exact absurd (bfct_reach_isolated hiso h.symm) (by decide)


theorem bfct_transport_witness :
    ¬ (bkg_deleteVertex (bfct_restrict bfct_star bfct_starS)
        (⟨0, by decide⟩ : {v // v ∈ bfct_starS})).Reachable
        (⟨1, by decide⟩ : {v // v ∈ bfct_starS}) (⟨2, by decide⟩ : {v // v ∈ bfct_starS}) :=
  bfct_cut_transport (by
    show ¬ (bkg_deleteVertex bfct_star (0 : Fin 4)).Reachable 1 2
    exact bfct_star_cut)

#check @bfct_transport_witness


theorem bfct_status :
    
    (∀ {V : Type} {G : SimpleGraph V} {S : Finset V} {t a b : {v // v ∈ S}},
      ¬ (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V) →
      ¬ (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b) ∧
    
    (∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
      {T : SimpleGraph {v // v ∈ S}} [_i : DecidableRel T.Adj],
      T ≤ bfct_restrict G S → T.IsTree →
      ∀ {ι : Type} [Fintype ι] (f : ι → {v // v ∈ S}), Function.Injective f →
      (∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₂ : V) ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₃ : V) ∧
        ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₂ : V) (a₃ : V)) →
      ∀ (B : Finset {v // v ∈ S}), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bao_AllOpenTrif ω L →
      ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧
        ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V G S t a b h; exact bfct_cut_transport h
  · intro V _ G _ S T _ hTH hT ι _ f hf hcut B hleaf
    exact bfct_count G S hTH hT f hf hcut B hleaf
  · intro ω L h; exact bgf2_trif_separation h

#check @bfct_status

end StatMech.Walls
