/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteCutConditionalTwoPoint_eq_div
    (beta : Real) (S : Finset V)
    (outside : {v : V // v ∉ S} → Bool)
    (x y : {v : V // v ∈ S}) :
    finiteCutConditionalTwoPoint G beta S outside x y =
      finiteCutConditionalPairNumerator G beta S outside x y /
        finiteCutConditionalZ G beta S outside := by
  rfl


theorem ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ
    (beta : Real) (S : Finset V) :
    ZJ G.edgeFinset (fun _ => beta) (fun _ => 0) =
      ∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalZ G beta S outside := by
  unfold ZJ
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun sigma => wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Prod.fst, Prod.snd]
  apply Finset.sum_congr rfl
  intro outside _
  unfold finiteCutConditionalZ ZJ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inside _
  change wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
      (finiteCutMerge S inside outside) = _
  rw [wJ_finiteCutMerge_factor_fixedExterior]


theorem sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator
    (beta : Real) (S : Finset V) (x y : {v : V // v ∈ S}) :
    (∑ sigma : ConfigSpace V,
        (spin sigma x.1 * spin sigma y.1) *
          wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma) =
      ∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalPairNumerator G beta S outside x y := by
  rw [← Equiv.sum_comp (ghsvp_splitConfig S).symm
    (fun sigma => (spin sigma x.1 * spin sigma y.1) *
      wJ G.edgeFinset (fun _ => beta) (fun _ => 0) sigma)]
  simp only [ghsvp_splitConfig, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Prod.fst, Prod.snd]
  apply Finset.sum_congr rfl
  intro outside _
  unfold finiteCutConditionalPairNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro inside _
  change (spin (finiteCutMerge S inside outside) x.1 *
      spin (finiteCutMerge S inside outside) y.1) *
        wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
          (finiteCutMerge S inside outside) = _
  rw [spin_finiteCutMerge_inside, spin_finiteCutMerge_inside,
    wJ_finiteCutMerge_factor_fixedExterior]
  ring


theorem expJ_pair_le_finiteCutPlusTwoPoint
    (beta : Real) (hbeta : 0 ≤ beta) (S : Finset V)
    (x y : {v : V // v ∈ S}) :
    expJ G.edgeFinset (fun _ => beta) (fun _ => 0)
        (fun sigma => spin sigma x.1 * spin sigma y.1) ≤
      finiteCutPlusTwoPoint G beta S x y := by
  let P := finiteCutPlusTwoPoint G beta S x y
  have hcond (outside : {v : V // v ∉ S} → Bool) :
      finiteCutConditionalPairNumerator G beta S outside x y ≤
        P * finiteCutConditionalZ G beta S outside := by
    have hle := finiteCutConditionalTwoPoint_le_plus
      G beta hbeta S outside x y
    rw [finiteCutConditionalTwoPoint_eq_div] at hle
    exact (div_le_iff₀ (ZJ_pos (finiteCutGraph G S).edgeFinset
      (fun _ => beta)
      (fun z => beta * finiteCutBoundaryField G S outside z))).mp hle
  unfold expJ
  rw [sum_pair_wJ_eq_sum_finiteCutExteriorFactor_mul_conditionalNumerator]
  change _ ≤ P
  apply (div_le_iff₀ (ZJ_pos G.edgeFinset (fun _ => beta) (fun _ => 0))).2
  calc
    (∑ outside : {v : V // v ∉ S} → Bool,
        finiteCutExteriorFactor G beta S outside *
          finiteCutConditionalPairNumerator G beta S outside x y) ≤
        ∑ outside : {v : V // v ∉ S} → Bool,
          finiteCutExteriorFactor G beta S outside *
            (P * finiteCutConditionalZ G beta S outside) := by
      exact Finset.sum_le_sum fun outside _ =>
        mul_le_mul_of_nonneg_left (hcond outside)
          (finiteCutExteriorFactor_pos G beta S outside).le
    _ = P * ∑ outside : {v : V // v ∉ S} → Bool,
          finiteCutExteriorFactor G beta S outside *
            finiteCutConditionalZ G beta S outside := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro outside _
      ring
    _ = P * ZJ G.edgeFinset (fun _ => beta) (fun _ => 0) := by
      rw [ZJ_eq_sum_finiteCutExteriorFactor_mul_conditionalZ]


theorem isingTorusTwoPoint_le_finiteCutPlus
    {d k : Nat} (beta : Real) (hbeta : 0 ≤ beta)
    (S : Finset (IsingDyadicTorus d k)) (x y : {v // v ∈ S}) :
    isingTorusTwoPoint beta x.1 y.1 ≤
      finiteCutPlusTwoPoint (isingTorusGraph d k) beta S x y := by
  rw [isingTorusTwoPoint_eq_twoPointJ]
  unfold twoPointJ
  rw [expectationJ_eq_expJ]
  simp only [mul_one]
  have hle := expJ_pair_le_finiteCutPlusTwoPoint
    (isingTorusGraph d k) beta hbeta S x y
  have hfun : spinProd (sourcePair x.1 y.1) =
      fun sigma => spin sigma x.1 * spin sigma y.1 := by
    funext sigma
    exact spinProd_sourcePair sigma x.1 y.1
  rw [hfun]
  exact hle


theorem finiteCutPlusTwoPoint_eq_vertexFieldTwoPoint
    (beta : Real) (S : Finset V) (x y : {v // v ∈ S}) :
    finiteCutPlusTwoPoint G beta S x y =
      vertexFieldTwoPoint (finiteCutGraph G S) beta
        (unitEdgeCoupling (finiteCutGraph G S))
        (finiteCutPlusBoundaryField G S) x y := by
  unfold finiteCutPlusTwoPoint vertexFieldTwoPoint vertexFieldExpectation
  have hweight (sigma : ConfigSpace {v : V // v ∈ S}) :
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
          (fun z => beta * finiteCutPlusBoundaryField G S z) sigma =
        vertexFieldWeight (finiteCutGraph G S) beta
          (unitEdgeCoupling (finiteCutGraph G S))
          (finiteCutPlusBoundaryField G S) sigma := by
    unfold wJ vertexFieldWeight
    congr 1
    have hedge : (∑ e ∈ (finiteCutGraph G S).edgeFinset,
        unitEdgeCoupling (finiteCutGraph G S) e * bond sigma e) =
        ∑ e ∈ (finiteCutGraph G S).edgeFinset, bond sigma e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [unitEdgeCoupling_edgeFinset (finiteCutGraph G S) he, one_mul]
    rw [hedge, mul_add]
    simp_rw [Finset.mul_sum]
    ring
  have hZ : ZJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
      (fun z => beta * finiteCutPlusBoundaryField G S z) =
      vertexFieldZ (finiteCutGraph G S) beta
        (unitEdgeCoupling (finiteCutGraph G S))
        (finiteCutPlusBoundaryField G S) := by
    unfold ZJ vertexFieldZ
    exact Finset.sum_congr rfl fun sigma _ => hweight sigma
  unfold expJ
  rw [hZ]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma _
  rw [spinProd_sourcePair, hweight]


theorem expJ_pair_beta_field_eq_vertexFieldTwoPoint
    (beta : Real) (field : V → Real) (x y : V) :
    expJ G.edgeFinset (fun _ => beta) (fun z => beta * field z)
        (fun sigma => spin sigma x * spin sigma y) =
      vertexFieldTwoPoint G beta (unitEdgeCoupling G) field x y := by
  unfold expJ vertexFieldTwoPoint vertexFieldExpectation
  have hweight (sigma : ConfigSpace V) :
      wJ G.edgeFinset (fun _ => beta) (fun z => beta * field z) sigma =
        vertexFieldWeight G beta (unitEdgeCoupling G) field sigma := by
    unfold wJ vertexFieldWeight
    congr 1
    have hedge : (∑ e ∈ G.edgeFinset,
        unitEdgeCoupling G e * bond sigma e) =
        ∑ e ∈ G.edgeFinset, bond sigma e := by
      apply Finset.sum_congr rfl
      intro e he
      rw [unitEdgeCoupling_edgeFinset G he, one_mul]
    rw [hedge, mul_add]
    simp_rw [Finset.mul_sum]
    ring
  have hZ : ZJ G.edgeFinset (fun _ => beta) (fun z => beta * field z) =
      vertexFieldZ G beta (unitEdgeCoupling G) field := by
    unfold ZJ vertexFieldZ
    exact Finset.sum_congr rfl fun sigma _ => hweight sigma
  rw [hZ]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma _
  rw [spinProd_sourcePair, hweight]

section Relabel

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]


theorem expJ_pair_const_relabel (e : V ≃ W)
    (hadj : ∀ x y, G.Adj x y ↔ H.Adj (e x) (e y))
    (beta : Real) (fieldV : V → Real) (fieldW : W → Real)
    (hfield : ∀ x, fieldV x = fieldW (e x)) (x y : V) :
    expJ G.edgeFinset (fun _ => beta) fieldV
        (fun sigma => spin sigma x * spin sigma y) =
      expJ H.edgeFinset (fun _ => beta) fieldW
        (fun sigma => spin sigma (e x) * spin sigma (e y)) := by
  unfold expJ
  rw [ghsi_ZJ_const_relabel G H e hadj beta fieldV fieldW hfield]
  rw [← Equiv.sum_comp (isingCfgEquiv e)
    (fun omega => (spin omega x * spin omega y) *
      wJ G.edgeFinset (fun _ => beta) fieldV omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro omega _
  rw [spin_isingCfgEquiv, spin_isingCfgEquiv,
    ghsi_wJ_const_relabel G H e hadj beta fieldV fieldW hfield]


theorem finiteCutPlusTwoPoint_relabel
    (S : Finset V) (T : Finset W)
    (e : {v : V // v ∈ S} ≃ {w : W // w ∈ T})
    (hadj : ∀ x y,
      (finiteCutGraph G S).Adj x y ↔
        (finiteCutGraph H T).Adj (e x) (e y))
    (hfield : ∀ x, finiteCutPlusBoundaryField G S x =
      finiteCutPlusBoundaryField H T (e x))
    (beta : Real) (x y : {v : V // v ∈ S}) :
    finiteCutPlusTwoPoint G beta S x y =
      finiteCutPlusTwoPoint H beta T (e x) (e y) := by
  unfold finiteCutPlusTwoPoint
  apply expJ_pair_const_relabel
    (finiteCutGraph G S) (finiteCutGraph H T) e hadj beta
      (fun z => beta * finiteCutPlusBoundaryField G S z)
      (fun z => beta * finiteCutPlusBoundaryField H T z)
      (fun z => congrArg (fun r : Real => beta * r) (hfield z)) x y

end Relabel


theorem finiteCutPlusTwoPoint_torusImage_eq_gvPlus_of_field
    {d k R : Nat} (S : Finset (Site d))
    (hS : (↑S : Set (Site d)) ⊆ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
    (hfield : ∀ x : {x // x ∈ S},
      finiteCutPlusBoundaryField (isingTorusGraph d k)
          (isingTorusImageFinset k S) (isingTorusImageEquiv S hinj x) =
        plusBoundaryField S x)
    (beta : Real) (a b : {x // x ∈ S}) :
    finiteCutPlusTwoPoint (isingTorusGraph d k) beta
        (isingTorusImageFinset k S)
        (isingTorusImageEquiv S hinj a)
        (isingTorusImageEquiv S hinj b) =
      ∫ omega, spin omega a.1 * spin omega b.1 ∂(gvPlusMeasure S beta 0) := by
  let e := isingTorusImageEquiv S hinj
  have hadj : ∀ u v : {z // z ∈ isingTorusImageFinset k S},
      (finiteCutGraph (isingTorusGraph d k)
          (isingTorusImageFinset k S)).Adj u v ↔
        (graphS d S).Adj (e.symm u) (e.symm v) := by
    intro u v
    change (isingTorusGraph d k).Adj u.1 v.1 ↔
      (graphS d S).Adj (e.symm u) (e.symm v)
    simpa only [e, Equiv.apply_symm_apply] using
      (isingTorusImageEquiv_adj S hS hside hinj
        (e.symm u) (e.symm v)).symm
  have hfield' : ∀ u : {z // z ∈ isingTorusImageFinset k S},
      beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
          (isingTorusImageFinset k S) u =
        beta * plusBoundaryField S (e.symm u) := by
    intro u
    apply congrArg (fun r : Real => beta * r)
    simpa only [e, Equiv.apply_symm_apply] using hfield (e.symm u)
  unfold finiteCutPlusTwoPoint
  calc
    expJ (finiteCutGraph (isingTorusGraph d k)
          (isingTorusImageFinset k S)).edgeFinset
        (fun _ => beta)
        (fun z => beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
          (isingTorusImageFinset k S) z)
        (fun sigma => spin sigma (e a) * spin sigma (e b)) =
      expJ (graphS d S).edgeFinset (fun _ => beta)
        (fun z => beta * plusBoundaryField S z)
        (fun sigma => spin sigma a * spin sigma b) := by
          simpa only [Equiv.symm_apply_apply] using expJ_pair_const_relabel
            (finiteCutGraph (isingTorusGraph d k)
              (isingTorusImageFinset k S))
            (graphS d S) e.symm hadj beta
            (fun z => beta * finiteCutPlusBoundaryField (isingTorusGraph d k)
              (isingTorusImageFinset k S) z)
            (fun z => beta * plusBoundaryField S z) hfield' (e a) (e b)
    _ = vertexFieldTwoPoint (graphS d S) beta
        (unitEdgeCoupling (graphS d S)) (plusBoundaryField S) a b :=
      expJ_pair_beta_field_eq_vertexFieldTwoPoint
        (graphS d S) beta (plusBoundaryField S) a b
    _ = ∫ omega, spin omega a.1 * spin omega b.1
        ∂(gvPlusMeasure S beta 0) :=
      (gvPlus_pair_eq_vertexField S beta a b).symm


end
end StatMech.FrontierA
