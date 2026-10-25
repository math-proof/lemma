/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc87brerouteinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Def.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc87b_tri_sources :
    sources gc87b_triEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide


theorem gc87b_one_le_ncount_empty (ends : ι → Sym2 W) (R : Finset ι) :
    1 ≤ gc86b_ncount ends R ∅ := by
  unfold gc86b_ncount
  rw [Finset.one_le_card]
  refine ⟨∅, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
  ext v; simp [RandomCurrent.sources, degK]


theorem gc87b_one_le_T3_of_allConn (ends : ι → Sym2 W) (m : Finset ι) {o x y g : W}
    (hcx : connK ends m o x) (hcy : connK ends m o y) (hcg : connK ends m o g) :
    1 ≤ gc87b_T3 ends m o x y g := by
  unfold gc87b_T3
  have hmem : (∅ : Finset ι) ∈ (m.powerset.filter (fun K => sources ends K = ∅)).filter
      (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g) := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and,
      Finset.sdiff_empty]
    refine ⟨?_, hcx, hcy, hcg⟩
    ext v; simp [RandomCurrent.sources, degK]
  calc (1 : ℕ) ≤ gc86b_ncount ends (m \ ∅) ∅ := by rw [Finset.sdiff_empty]; exact gc87b_one_le_ncount_empty ends m
    _ ≤ _ := Finset.single_le_sum (f := fun J₁ => gc86b_ncount ends (m \ J₁) ∅)
              (fun _ _ => Nat.zero_le _) hmem


theorem gc87b_tri_residue_nonvacuous :
    gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1
      ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
  have hcog : gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1 := by
    unfold gc85b_pcount; decide
  refine ⟨hcog, ?_⟩
  
  unfold gc87b_CogxgLeT3
  rw [hcog]
  refine gc87b_one_le_T3_of_allConn gc87b_triEnds (univ : Finset (Fin 3)) ?_ ?_ ?_
  
  · refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  
  · refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  
  · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩


theorem gc87b_local_template_insufficient :
    ∃ (nS nT : ℕ) (adj : Fin nS → Fin nT → Prop),
      
      nS ≤ nT
      
      ∧ ∃ (fixedChoice : Fin nS → Fin nT), ¬ Function.Injective fixedChoice := by
  
  
  refine ⟨2, 2, fun _ _ => True, le_refl 2, fun _ => 0, ?_⟩
  intro hinj
  have := hinj (a₁ := 0) (a₂ := 1) rfl
  simp at this


theorem gc87b_cogxg_le_T3_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g) :
    
    (gc85b_pcount ends m {o, g} {x, g}
        = ∑ K₁ ∈ (m.powerset.filter (fun K => sources ends K = {o, g})).filter
            (fun K₁ => connK ends (m \ K₁) x g),
          gc86b_ncount ends (m \ K₁) ∅)
    
    ∧ (2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g)
    
    ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨gc87b_cogxg_fiber_conn (o := o) (x := x) (y := y) (g := g) ends m hnd hxg,
   gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog,
   fun hle => gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle⟩

end StatMech.Walls
