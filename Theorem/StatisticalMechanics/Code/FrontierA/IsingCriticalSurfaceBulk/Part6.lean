/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalSurfaceBulk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalBoundaryInfluence.Part4
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectionGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalSurfaceBulk.Part5
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Lattice StatMech.ConfigSpace
  StatMech.Sharpness

noncomputable section

theorem unequalReplicaBridgeMoment_pos
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    0 < unequalReplicaBridgeMoment G H K J hf hg r := by
  unfold unequalReplicaBridgeMoment
  apply div_pos
  · apply Finset.sum_pos
    · intro a _
      apply Finset.sum_pos
      · intro b _
        exact mul_pos (mul_pos (wJ_pos _ _ _ _) (wJ_pos _ _ _ _))
          (Real.exp_pos _)
      · exact Finset.univ_nonempty
    · exact Finset.univ_nonempty
  · exact mul_pos (ZJ_pos _ _ _) (ZJ_pos _ _ _)


theorem wJ_crossInterface_factor
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (a : ConfigSpace V) (b : ConfigSpace W) :
    wJ K.edgeFinset (fun _ => J) (Sum.elim hf hg)
        (isingSumConfigEquiv.symm (a, b)) =
      wJ G.edgeFinset (fun _ => J) hf a *
        wJ H.edgeFinset (fun _ => J) hg b *
        Real.exp (J * unequalReplicaBridgeInteraction G H K a b) := by
  classical
  unfold wJ unequalReplicaBridgeInteraction
  have hdisj : Disjoint ((G ⊕g H).edgeFinset)
      (StatMech.FK.fis_interface G H K) := by
    rw [StatMech.FK.fis_interface]
    exact Finset.disjoint_sdiff
  rw [StatMech.FK.fis_edgeFinset_eq hcross,
    Finset.sum_union hdisj]
  have hsumBase : (∑ e ∈ (G ⊕g H).edgeFinset,
        J * bond (isingSumConfigEquiv.symm (a, b)) e) =
      J * ∑ e ∈ (G ⊕g H).edgeFinset,
        bond (isingSumConfigEquiv.symm (a, b)) e := by
    rw [Finset.mul_sum]
  have hsumInterface : (∑ e ∈ StatMech.FK.fis_interface G H K,
        J * bond (isingSumConfigEquiv.symm (a, b)) e) =
      J * ∑ e ∈ StatMech.FK.fis_interface G H K,
        bond (isingSumConfigEquiv.symm (a, b)) e := by
    rw [Finset.mul_sum]
  rw [hsumBase, hsumInterface,
    StatMech.Ising.sum_bond_isingSumConfigEquiv_symm]
  simp only [Fintype.sum_sum_type, spin_isingSumConfigEquiv_symm_inl,
    spin_isingSumConfigEquiv_symm_inr]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hG : J * ∑ e ∈ G.edgeFinset, bond a e =
      ∑ e ∈ G.edgeFinset, J * bond a e := by
    simpa using (Finset.mul_sum G.edgeFinset (fun e => bond a e) J)
  have hH : J * ∑ e ∈ H.edgeFinset, bond b e =
      ∑ e ∈ H.edgeFinset, J * bond b e := by
    simpa using (Finset.mul_sum H.edgeFinset (fun e => bond b e) J)
  rw [mul_add, hG, hH]
  ring


theorem ZJ_crossInterface_eq_mul_unequalMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    ZJ K.edgeFinset (fun _ => J) (Sum.elim hf hg) =
      ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg *
          unequalReplicaBridgeMoment G H K J hf hg J := by
  unfold ZJ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [wJ_crossInterface_factor G H K hcross J hf hg]
  unfold unequalReplicaBridgeMoment
  have hZG : ZJ G.edgeFinset (fun _ => J) hf ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  have hZH : ZJ H.edgeFinset (fun _ => J) hg ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  unfold ZJ at hZG hZH ⊢
  field_simp [hZG, hZH]


theorem unequalReplicaBridgeInteraction_flip_right
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (a : ConfigSpace V) (b : ConfigSpace W) :
    unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) =
      -unequalReplicaBridgeInteraction G H K a b := by
  classical
  unfold unequalReplicaBridgeInteraction
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
      change s(x, y) ∈ K.edgeFinset \ (G ⊕g H).edgeFinset at he
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeFinset] at he
      obtain ⟨hK, hnot⟩ := he
      rcases x with x | x <;> rcases y with y | y
      · exact absurd
          (show (G ⊕g H).Adj (Sum.inl x) (Sum.inl y) from
            hcross.inl x y hK) hnot
      · rw [bond_mk, bond_mk,
          spin_isingSumConfigEquiv_symm_inl,
          spin_isingSumConfigEquiv_symm_inr,
          spin_isingSumConfigEquiv_symm_inl,
          spin_isingSumConfigEquiv_symm_inr,
          FieldGhostDict.spin_flipV]
        ring
      · rw [bond_mk, bond_mk,
          spin_isingSumConfigEquiv_symm_inr,
          spin_isingSumConfigEquiv_symm_inl,
          spin_isingSumConfigEquiv_symm_inr,
          spin_isingSumConfigEquiv_symm_inl,
          FieldGhostDict.spin_flipV]
        ring
      · exact absurd
          (show (G ⊕g H).Adj (Sum.inr x) (Sum.inr y) from
            hcross.inr x y hK) hnot

theorem unequalReplicaExp2_neg
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (F : ConfigSpace V -> ConfigSpace W -> Real) :
    unequalReplicaExp2 G H J hf hg (fun a b => -F a b) =
      -unequalReplicaExp2 G H J hf hg F := by
  unfold unequalReplicaExp2
  simp_rw [mul_neg]
  simp only [Finset.sum_neg_distrib]
  ring


theorem unequalReplicaExp2_flip_right
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (F : ConfigSpace V -> ConfigSpace W -> Real) :
    unequalReplicaExp2 G H J hf (fun x => -hg x) F =
      unequalReplicaExp2 G H J hf hg
        (fun a b => F a (FieldGhostDict.flipV b)) := by
  unfold unequalReplicaExp2
  rw [ghsvp_ZJ_negField]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive (V := W)).toPerm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.Involutive.coe_toPerm]
  rw [ghsvp_wJ_negField_flip]


theorem unequalReplicaBridgeMoment_neg_eq_negRightField
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeMoment G H K J hf hg (-r) =
      unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r := by
  change unequalReplicaExp2 G H J hf hg (fun a b =>
      Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) =
    unequalReplicaExp2 G H J hf (fun x => -hg x) (fun a b =>
      Real.exp (r * unequalReplicaBridgeInteraction G H K a b))
  rw [unequalReplicaExp2_flip_right]
  congr 1
  funext a b
  rw [unequalReplicaBridgeInteraction_flip_right G H K hcross]
  congr 1
  ring


theorem unequalReplicaBridgeMean_neg_eq_negRightField
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeMean G H K J hf hg (-r) =
      -unequalReplicaBridgeMean G H K J hf (fun x => -hg x) r := by
  unfold unequalReplicaBridgeMean
  change unequalReplicaExp2 G H J hf hg (fun a b =>
      unequalReplicaBridgeInteraction G H K a b *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf hg (-r) = _
  rw [unequalReplicaBridgeMoment_neg_eq_negRightField G H K hcross]
  change _ = -(unequalReplicaExp2 G H J hf (fun x => -hg x) (fun a b =>
      unequalReplicaBridgeInteraction G H K a b *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r)
  rw [unequalReplicaExp2_flip_right]
  have hobs : (fun a b =>
      unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a
          (FieldGhostDict.flipV b))) =
      (fun a b => -(unequalReplicaBridgeInteraction G H K a b *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b))) := by
    funext a b
    rw [unequalReplicaBridgeInteraction_flip_right G H K hcross]
    rw [show r * -unequalReplicaBridgeInteraction G H K a b =
        -r * unequalReplicaBridgeInteraction G H K a b by ring]
    ring
  rw [hobs, unequalReplicaExp2_neg]
  ring


theorem unequalReplicaBridgeVariance_neg_eq_negRightField
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    unequalReplicaBridgeVariance G H K J hf hg (-r) =
      unequalReplicaBridgeVariance G H K J hf (fun x => -hg x) r := by
  unfold unequalReplicaBridgeVariance
  change unequalReplicaExp2 G H J hf hg (fun a b =>
      unequalReplicaBridgeInteraction G H K a b ^ 2 *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf hg (-r) - _ = _
  rw [unequalReplicaBridgeMoment_neg_eq_negRightField G H K hcross,
    unequalReplicaBridgeMean_neg_eq_negRightField G H K hcross]
  change _ = unequalReplicaExp2 G H J hf (fun x => -hg x) (fun a b =>
      unequalReplicaBridgeInteraction G H K a b ^ 2 *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a b)) /
      unequalReplicaBridgeMoment G H K J hf (fun x => -hg x) r - _
  rw [unequalReplicaExp2_flip_right]
  have hobs : (fun a b =>
      unequalReplicaBridgeInteraction G H K a (FieldGhostDict.flipV b) ^ 2 *
        Real.exp (r * unequalReplicaBridgeInteraction G H K a
          (FieldGhostDict.flipV b))) =
      (fun a b => unequalReplicaBridgeInteraction G H K a b ^ 2 *
        Real.exp (-r * unequalReplicaBridgeInteraction G H K a b)) := by
    funext a b
    rw [unequalReplicaBridgeInteraction_flip_right G H K hcross]
    rw [show r * -unequalReplicaBridgeInteraction G H K a b =
        -r * unequalReplicaBridgeInteraction G H K a b by ring]
    ring
  rw [hobs]
  ring


theorem ZJ_crossInterface_negRight_eq_mul_unequalMoment_neg
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (hcross : StatMech.FK.fis_CrossInterface G H K)
    (J : Real) (hf : V -> Real) (hg : W -> Real) :
    ZJ K.edgeFinset (fun _ => J) (Sum.elim hf (fun x => -hg x)) =
      ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg *
          unequalReplicaBridgeMoment G H K J hf hg (-J) := by
  unfold ZJ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [wJ_crossInterface_factor G H K hcross J hf (fun x => -hg x)]
  have hinner (a : ConfigSpace V) :
      (∑ b : ConfigSpace W,
        wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
          Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) =
      ∑ b : ConfigSpace W,
        wJ H.edgeFinset (fun _ => J) hg b *
          Real.exp (-J * unequalReplicaBridgeInteraction G H K a b) := by
    rw [← Equiv.sum_comp
      (FieldGhostDict.flipV_involutive (V := W)).toPerm]
    apply Finset.sum_congr rfl
    intro b _
    change wJ H.edgeFinset (fun _ => J) (fun x => -hg x)
          (FieldGhostDict.flipV b) *
        Real.exp (J * unequalReplicaBridgeInteraction G H K a
          (FieldGhostDict.flipV b)) = _
    rw [ghsvp_wJ_negField_flip,
      unequalReplicaBridgeInteraction_flip_right G H K hcross]
    congr 1
    ring_nf
  have hdouble :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
          Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) =
      ∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
          Real.exp (-J * unequalReplicaBridgeInteraction G H K a b) := by
    apply Finset.sum_congr rfl
    intro a _
    calc
      (∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
              wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
            Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) =
          wJ G.edgeFinset (fun _ => J) hf a *
            (∑ b : ConfigSpace W,
              wJ H.edgeFinset (fun _ => J) (fun x => -hg x) b *
                Real.exp (J * unequalReplicaBridgeInteraction G H K a b)) := by
            rw [Finset.mul_sum]
            simp only [mul_assoc]
      _ = wJ G.edgeFinset (fun _ => J) hf a *
            (∑ b : ConfigSpace W,
              wJ H.edgeFinset (fun _ => J) hg b *
                Real.exp (-J * unequalReplicaBridgeInteraction G H K a b)) := by
            rw [hinner]
      _ = ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
              wJ H.edgeFinset (fun _ => J) hg b *
            Real.exp (-J * unequalReplicaBridgeInteraction G H K a b) := by
            rw [Finset.mul_sum]
            simp only [mul_assoc]
  rw [hdouble]
  unfold unequalReplicaBridgeMoment
  have hZG : ZJ G.edgeFinset (fun _ => J) hf ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  have hZH : ZJ H.edgeFinset (fun _ => J) hg ≠ 0 :=
    (ZJ_pos _ _ _).ne'
  unfold ZJ at hZG hZH ⊢
  field_simp [hZG, hZH]

theorem hasDerivAt_unequalReplicaBridgeMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (unequalReplicaBridgeMoment G H K J hf hg)
      ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            (unequalReplicaBridgeInteraction G H K a b *
              Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
        (ZJ G.edgeFinset (fun _ => J) hf *
          ZJ H.edgeFinset (fun _ => J) hg)) r := by
  unfold unequalReplicaBridgeMoment
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  have hexp : HasDerivAt
      (fun t : Real => Real.exp
        (t * unequalReplicaBridgeInteraction G H K a b))
      (Real.exp (r * unequalReplicaBridgeInteraction G H K a b) *
        unequalReplicaBridgeInteraction G H K a b) r := by
    simpa using (Real.hasDerivAt_exp
      (r * unequalReplicaBridgeInteraction G H K a b)).comp r
        ((hasDerivAt_id r).mul_const
          (unequalReplicaBridgeInteraction G H K a b))
  convert hexp.const_mul
    (wJ G.edgeFinset (fun _ => J) hf a *
      wJ H.edgeFinset (fun _ => J) hg b) using 1 <;> ring

theorem hasDerivAt_unequalReplicaBridgeWeightedMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (fun t =>
      ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            (unequalReplicaBridgeInteraction G H K a b *
              Real.exp (t * unequalReplicaBridgeInteraction G H K a b))) /
        (ZJ G.edgeFinset (fun _ => J) hf *
          ZJ H.edgeFinset (fun _ => J) hg)))
      ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
          wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            (unequalReplicaBridgeInteraction G H K a b ^ 2 *
              Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
        (ZJ G.edgeFinset (fun _ => J) hf *
          ZJ H.edgeFinset (fun _ => J) hg)) r := by
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  have hexp : HasDerivAt
      (fun t : Real => Real.exp
        (t * unequalReplicaBridgeInteraction G H K a b))
      (Real.exp (r * unequalReplicaBridgeInteraction G H K a b) *
        unequalReplicaBridgeInteraction G H K a b) r := by
    simpa using (Real.hasDerivAt_exp
      (r * unequalReplicaBridgeInteraction G H K a b)).comp r
        ((hasDerivAt_id r).mul_const
          (unequalReplicaBridgeInteraction G H K a b))
  convert (hexp.const_mul
      (unequalReplicaBridgeInteraction G H K a b)).const_mul
    (wJ G.edgeFinset (fun _ => J) hf a *
      wJ H.edgeFinset (fun _ => J) hg b) using 1 <;> ring


theorem hasDerivAt_unequalReplicaBridgeMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (unequalReplicaBridgeMean G H K J hf hg)
      (unequalReplicaBridgeVariance G H K J hf hg r) r := by
  let N : Real -> Real := fun t =>
    ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
          wJ H.edgeFinset (fun _ => J) hg b *
          (unequalReplicaBridgeInteraction G H K a b *
            Real.exp (t * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg))
  let N2 : Real :=
    ((∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
          wJ H.edgeFinset (fun _ => J) hg b *
          (unequalReplicaBridgeInteraction G H K a b ^ 2 *
            Real.exp (r * unequalReplicaBridgeInteraction G H K a b))) /
      (ZJ G.edgeFinset (fun _ => J) hf *
        ZJ H.edgeFinset (fun _ => J) hg))
  let M := unequalReplicaBridgeMoment G H K J hf hg r
  have hN : HasDerivAt N N2 r := by
    simpa only [N, N2] using
      hasDerivAt_unequalReplicaBridgeWeightedMean G H K J hf hg r
  have hM := hasDerivAt_unequalReplicaBridgeMoment G H K J hf hg r
  have hMne : M ≠ 0 :=
    (unequalReplicaBridgeMoment_pos G H K J hf hg r).ne'
  have hquot := hN.div hM hMne
  change HasDerivAt (N / unequalReplicaBridgeMoment G H K J hf hg)
    (unequalReplicaBridgeVariance G H K J hf hg r) r
  convert hquot using 1
  unfold unequalReplicaBridgeVariance unequalReplicaBridgeMean
  dsimp only [N, N2, M]
  field_simp [(unequalReplicaBridgeMoment_pos G H K J hf hg r).ne',
    (ZJ_pos G.edgeFinset (fun _ => J) hf).ne',
    (ZJ_pos H.edgeFinset (fun _ => J) hg).ne']
  have hsecond :
      (∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            unequalReplicaBridgeInteraction G H K a b ^ 2 *
          Real.exp (unequalReplicaBridgeInteraction G H K a b * r)) =
      ∑ a : ConfigSpace V, ∑ b : ConfigSpace W,
        wJ G.edgeFinset (fun _ => J) hf a *
            wJ H.edgeFinset (fun _ => J) hg b *
            unequalReplicaBridgeInteraction G H K a b ^ 2 *
          Real.exp (r * unequalReplicaBridgeInteraction G H K a b) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm (unequalReplicaBridgeInteraction G H K a b) r]
  rw [hsecond]
  ring

theorem hasDerivAt_log_unequalReplicaBridgeMoment
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (fun t =>
      Real.log (unequalReplicaBridgeMoment G H K J hf hg t))
      (unequalReplicaBridgeMean G H K J hf hg r) r := by
  exact (hasDerivAt_unequalReplicaBridgeMoment G H K J hf hg r).log
    (unequalReplicaBridgeMoment_pos G H K J hf hg r).ne'

theorem hasDerivAt_unequalReplicaBridgeFreeEnergy
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (unequalReplicaBridgeFreeEnergy G H K J hf hg)
      (unequalReplicaBridgeMean G H K J hf hg r +
        unequalReplicaBridgeMean G H K J hf hg (-r)) r := by
  unfold unequalReplicaBridgeFreeEnergy
  have hp := hasDerivAt_log_unequalReplicaBridgeMoment
    G H K J hf hg r
  have hm := (hasDerivAt_log_unequalReplicaBridgeMoment
    G H K J hf hg (-r)).comp r (hasDerivAt_id r).neg
  convert hp.sub hm using 1 <;> ring

theorem hasDerivAt_unequalReplicaBridgeSymmetricMean
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real) (r : Real) :
    HasDerivAt (fun t =>
      unequalReplicaBridgeMean G H K J hf hg t +
        unequalReplicaBridgeMean G H K J hf hg (-t))
      (unequalReplicaBridgeVariance G H K J hf hg r -
        unequalReplicaBridgeVariance G H K J hf hg (-r)) r := by
  have hp := hasDerivAt_unequalReplicaBridgeMean G H K J hf hg r
  have hm := (hasDerivAt_unequalReplicaBridgeMean
    G H K J hf hg (-r)).comp r (hasDerivAt_id r).neg
  convert hp.add hm using 1 <;> ring


theorem unequalReplicaBridgeFreeEnergy_le_of_variance_order
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (K : SimpleGraph (V ⊕ W)) [DecidableRel K.Adj]
    (J : Real) (hf : V -> Real) (hg : W -> Real)
    (r : Real) (hr : 0 <= r)
    (hvar : forall t, 0 <= t ->
      unequalReplicaBridgeVariance G H K J hf hg t <=
        unequalReplicaBridgeVariance G H K J hf hg (-t)) :
    unequalReplicaBridgeFreeEnergy G H K J hf hg r <=
      2 * r * unequalReplicaBridgeMean G H K J hf hg 0 := by
  let D : Real -> Real := fun t =>
    unequalReplicaBridgeMean G H K J hf hg t +
      unequalReplicaBridgeMean G H K J hf hg (-t)
  have hdiffD : Differentiable Real D := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
      G H K J hf hg t).differentiableAt
  have hanti : AntitoneOn D (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici (0 : Real))
    · exact hdiffD.continuous.continuousOn
    · intro t _
      exact (hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hasDerivAt_unequalReplicaBridgeSymmetricMean
        G H K J hf hg t).deriv]
      exact sub_nonpos.mpr (hvar t ht.le)
  have hmean : forall t, 0 <= t -> D t <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    intro t ht
    have hle := hanti (by simp) ht ht
    dsimp only [D] at hle
    rw [neg_zero] at hle
    linarith
  rcases hr.eq_or_lt with rfl | hrpos
  · simp [unequalReplicaBridgeFreeEnergy]
  have hdiffAll : Differentiable Real
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) := by
    intro t
    exact (hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg t).differentiableAt
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope
    (unequalReplicaBridgeFreeEnergy G H K J hf hg) hrpos
    hdiffAll.continuous.continuousOn hdiffAll.differentiableOn
  have hderiv : deriv
      (unequalReplicaBridgeFreeEnergy G H K J hf hg) c <=
      2 * unequalReplicaBridgeMean G H K J hf hg 0 := by
    rw [(hasDerivAt_unequalReplicaBridgeFreeEnergy
      G H K J hf hg c).deriv]
    exact hmean c hc.1.le
  have hzero : unequalReplicaBridgeFreeEnergy G H K J hf hg 0 = 0 := by
    simp [unequalReplicaBridgeFreeEnergy]
  have hmul := mul_le_mul_of_nonneg_right hderiv hrpos.le
  rw [hslope, hzero] at hmul
  simp only [sub_zero] at hmul
  rw [div_mul_cancel₀ _ hrpos.ne'] at hmul
  convert hmul using 1 <;> ring


end
end StatMech.FrontierA
