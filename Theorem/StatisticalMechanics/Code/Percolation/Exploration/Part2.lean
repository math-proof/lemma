/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.Exploration.Part2
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem part_norm (p : ℝ≥0) (hp : p ≤ 1) (Sₜ : Type*) [Fintype Sₜ] [DecidableEq Sₜ] :
    (∑ x : Sₜ → Bool, ∏ i, w1 p hp (x i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : Sₜ) (b : Bool) => w1 p hp b)]
  have h : ∀ _ : Sₜ, (∑ b : Bool, w1 p hp b) = 1 := fun _ => w1_sum p hp
  rw [Finset.prod_congr rfl (fun i _ => h i)]; simp


theorem wsum_mul (p : ℝ≥0) (hp : p ≤ 1) (P : E → Prop) [DecidablePred P]
    (f g : ConfigSpace E → ℝ)
    (hf : ∀ ω ω', (∀ e, P e → ω e = ω' e) → f ω = f ω')
    (hg : ∀ ω ω', (∀ e, ¬ P e → ω e = ω' e) → g ω = g ω') :
    wsum p hp (fun ω => f ω * g ω) = wsum p hp f * wsum p hp g := by
  classical
  set ee := Equiv.piEquivPiSubtypeProd P (fun _ : E => Bool) with hee
  have hsymm : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool) (e : E),
      ee.symm (a, b) e = if h : P e then a ⟨e, h⟩ else b ⟨e, h⟩ := fun _ _ _ => rfl
  have hWfac : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool),
      W p hp (ee.symm (a, b))
        = (∏ i : {x // P x}, w1 p hp (a i)) * (∏ i : {x // ¬ P x}, w1 p hp (b i)) := by
    intro a b
    unfold W
    rw [← Fintype.prod_subtype_mul_prod_subtype P (fun e => w1 p hp (ee.symm (a, b) e))]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hsymm]; simp [i.2])
    · exact Finset.prod_congr rfl (fun i _ => by rw [hsymm]; simp [i.2])
  have hffac : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool),
      f (ee.symm (a, b)) = f (ee.symm (a, fun _ => false)) :=
    fun a b => hf _ _ (fun e he => by rw [hsymm, hsymm]; simp [he])
  have hgfac : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool),
      g (ee.symm (a, b)) = g (ee.symm (fun _ => false, b)) :=
    fun a b => hg _ _ (fun e he => by rw [hsymm, hsymm]; simp [he])
  have reidx : ∀ (φ : ConfigSpace E → ℝ),
      (∑ ω : ConfigSpace E, φ ω)
        = ∑ x : (∀ i : {x // P x}, Bool) × (∀ i : {x // ¬ P x}, Bool), φ (ee.symm x) :=
    fun φ => (Equiv.sum_comp ee.symm φ).symm
  unfold wsum
  rw [reidx (fun ω => (f ω * g ω) * W p hp ω), reidx (fun ω => f ω * W p hp ω),
      reidx (fun ω => g ω * W p hp ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have lhs_eq :
      (∑ a, ∑ b, (f (ee.symm (a, b)) * g (ee.symm (a, b))) * W p hp (ee.symm (a, b)))
        = (∑ a, f (ee.symm (a, fun _ => false)) * (∏ i, w1 p hp (a i)))
          * (∑ b, g (ee.symm (fun _ => false, b)) * (∏ i, w1 p hp (b i))) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hWfac, hffac a b, hgfac a b]; ring
  have rhs1 :
      (∑ a, ∑ b, f (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = ∑ a, f (ee.symm (a, fun _ => false)) * (∏ i, w1 p hp (a i)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hstep : (∑ b, f (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = f (ee.symm (a, fun _ => false)) * (∏ i, w1 p hp (a i))
          * (∑ b : (∀ i : {x // ¬ P x}, Bool), ∏ i, w1 p hp (b i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [hWfac, hffac a b]; ring)
    rw [hstep, part_norm p hp]; ring
  have rhs2 :
      (∑ a, ∑ b, g (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = ∑ b, g (ee.symm (fun _ => false, b)) * (∏ i, w1 p hp (b i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hstep : (∑ a, g (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = g (ee.symm (fun _ => false, b)) * (∏ i, w1 p hp (b i))
          * (∑ a : (∀ i : {x // P x}, Bool), ∏ i, w1 p hp (a i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [hWfac, hgfac a b]; ring)
    rw [hstep, part_norm p hp]; ring
  rw [lhs_eq, rhs1, rhs2]


theorem real_eq_wsum (p : ℝ≥0) (hp : p ≤ 1) (A : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
      = wsum p hp (A.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [bernoulliProductMeasure.real_eq_sum A]
  unfold wsum W w1
  exact Finset.sum_congr rfl (fun ω _ => by rw [bernoulliProductMeasure.real_singleton ω])


theorem indep_cylinder (p : ℝ≥0) (hp : p ≤ 1) (P : E → Prop) [DecidablePred P]
    (A B : Set (ConfigSpace E))
    (hA : ∀ ω ω', (∀ e, P e → ω e = ω' e) → (ω ∈ A ↔ ω' ∈ A))
    (hB : ∀ ω ω', (∀ e, ¬ P e → ω e = ω' e) → (ω ∈ B ↔ ω' ∈ B)) :
    (bernoulliProductMeasure (E := E) p hp).real (A ∩ B)
      = (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  classical
  rw [real_eq_wsum, real_eq_wsum, real_eq_wsum]
  rw [show (A ∩ B).indicator (fun _ => (1 : ℝ))
        = fun ω => A.indicator (fun _ => (1:ℝ)) ω * B.indicator (fun _ => (1:ℝ)) ω from ?_]
  · apply wsum_mul p hp P
    · intro ω ω' hω
      by_cases hmem : ω ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hA ω ω' hω).mp hmem)]
      · rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem (fun hc => hmem ((hA ω ω' hω).mpr hc))]
    · intro ω ω' hω
      by_cases hmem : ω ∈ B
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hB ω ω' hω).mp hmem)]
      · rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem (fun hc => hmem ((hB ω ω' hω).mpr hc))]
  · funext ω
    rw [← Set.inter_indicator_mul (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω]; simp

end Finite


section Infinite

variable {E : Type*} [Countable E] [DecidableEq E]

omit [Countable E] [DecidableEq E] in

theorem indic_iff {X : Set (ConfigSpace E)} {a b : ConfigSpace E}
    (h : X.indicator (fun _ => (1:ℝ)) a = X.indicator (fun _ => (1:ℝ)) b) :
    (a ∈ X ↔ b ∈ X) := by
  by_cases ha : a ∈ X
  · rw [Set.indicator_of_mem ha] at h
    refine ⟨fun _ => ?_, fun _ => ha⟩
    by_contra hb; rw [Set.indicator_of_notMem hb] at h; norm_num at h
  · rw [Set.indicator_of_notMem ha] at h
    refine ⟨fun hc => absurd hc ha, fun hb => ?_⟩
    by_contra; rw [Set.indicator_of_mem hb] at h; norm_num at h


theorem indep_cylinder_inf (p : ℝ≥0) (hp : p ≤ 1)
    (A B : Set (ConfigSpace E)) (T U : Finset E) (hdisj : Disjoint T U)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real (A ∩ B)
      = (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  classical
  set F := T ∪ U with hF
  have hAF : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E) := hA.mono (by simp [hF])
  have hBF : DependsOn (B.indicator (fun _ => (1 : ℝ))) (F : Set E) := hB.mono (by simp [hF])
  have hcylA : A = cylinder F (F.restrict '' A) := eq_cylinder_restrict_image A F hAF
  have hcylB : B = cylinder F (F.restrict '' B) := eq_cylinder_restrict_image B F hBF
  
  have hmemA : ∀ (η : ConfigSpace ↥F),
      (η ∈ F.restrict '' A ↔ extendOff F (fun _ => false) η ∈ A) := by
    intro η
    refine ⟨fun hη => ?_, fun hext => ?_⟩
    · rw [hcylA, mem_cylinder, restrict_extendOff]; exact hη
    · have hc : extendOff F (fun _ => false) η ∈ cylinder F (F.restrict '' A) := hcylA ▸ hext
      rw [mem_cylinder, restrict_extendOff] at hc; exact hc
  have hmemB : ∀ (η : ConfigSpace ↥F),
      (η ∈ F.restrict '' B ↔ extendOff F (fun _ => false) η ∈ B) := by
    intro η
    refine ⟨fun hη => ?_, fun hext => ?_⟩
    · rw [hcylB, mem_cylinder, restrict_extendOff]; exact hη
    · have hc : extendOff F (fun _ => false) η ∈ cylinder F (F.restrict '' B) := hcylB ▸ hext
      rw [mem_cylinder, restrict_extendOff] at hc; exact hc
  
  have hAagree : ∀ η η' : ConfigSpace ↥F,
      (∀ j : ↥F, (j : E) ∈ T → η j = η' j) → (η ∈ F.restrict '' A ↔ η' ∈ F.restrict '' A) := by
    intro η η' hagr
    rw [hmemA, hmemA]
    refine indic_iff (hA (fun e heT => ?_))
    have heT' : e ∈ T := heT
    have heF : e ∈ F := Finset.mem_union.mpr (Or.inl heT')
    simp only [extendOff, heF, dif_pos]; exact hagr ⟨e, heF⟩ heT'
  have hBagree : ∀ η η' : ConfigSpace ↥F,
      (∀ j : ↥F, ¬ ((j : E) ∈ T) → η j = η' j) → (η ∈ F.restrict '' B ↔ η' ∈ F.restrict '' B) := by
    intro η η' hagr
    rw [hmemB, hmemB]
    refine indic_iff (hB (fun e heU => ?_))
    have heU' : e ∈ U := heU
    have heF : e ∈ F := Finset.mem_union.mpr (Or.inr heU')
    have heT : ¬ (e ∈ T) := fun hc => Finset.disjoint_left.mp hdisj hc heU'
    simp only [extendOff, heF, dif_pos]; exact hagr ⟨e, heF⟩ heT
  
  have hPA : (bernoulliProductMeasure (E := E) p hp).real A
      = (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' A) := by
    conv_lhs => rw [hcylA]; rw [realProb_cylinder]
  have hPB : (bernoulliProductMeasure (E := E) p hp).real B
      = (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' B) := by
    conv_lhs => rw [hcylB]; rw [realProb_cylinder]
  have hPAB : (bernoulliProductMeasure (E := E) p hp).real (A ∩ B)
      = (bernoulliProductMeasure (E := ↥F) p hp).real ((F.restrict '' A) ∩ (F.restrict '' B)) := by
    conv_lhs => rw [hcylA, hcylB, inter_cylinder_same]; rw [realProb_cylinder]
  rw [hPA, hPB, hPAB]
  exact indep_cylinder p hp (fun j : ↥F => (j : E) ∈ T)
    (F.restrict '' A) (F.restrict '' B) hAagree hBagree

end Infinite
end Percolation
end StatMech
