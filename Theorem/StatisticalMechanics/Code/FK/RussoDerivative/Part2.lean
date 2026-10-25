/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RussoDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.RussoDerivative.Part2
open scoped BigOperators


namespace StatMech

namespace FK

open Finset ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


lemma hasDerivAt_edgeProduct (ω : ConfigSpace (Sym2 V)) (p : ℝ) :
    HasDerivAt (fun p => edgeProduct G p ω)
      (∑ e ∈ G.edgeFinset, edgeProductOff G p e ω * (if ω e then (1 : ℝ) else -1)) p := by
  have h := HasDerivAt.finsetProd (u := G.edgeFinset)
    (f := fun (e : Sym2 V) (p : ℝ) => if ω e then p else 1 - p)
    (f' := fun (e : Sym2 V) => if ω e then (1 : ℝ) else -1)
    (x := p)
    (fun e _ => hasDerivAt_edgeFactor (V := V) ω e p)
  simp only [smul_eq_mul] at h
  have hfun : (fun p => edgeProduct G p ω)
      = (∏ i ∈ G.edgeFinset, fun (p : ℝ) => if ω i then p else 1 - p) := by
    funext q
    simp [edgeProduct, Finset.prod_apply]
  rw [hfun]
  refine h.congr_deriv ?_
  unfold edgeProductOff
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [mul_comm]


lemma edgeProduct_eq_off (p : ℝ) (e : Sym2 V) (ω : ConfigSpace (Sym2 V))
    (he : e ∈ G.edgeFinset) :
    edgeProduct G p ω = edgeProductOff G p e ω * (if ω e then p else 1 - p) := by
  unfold edgeProduct edgeProductOff
  rw [← Finset.prod_erase_mul G.edgeFinset _ he]


lemma edgeProductOff_term (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (e : Sym2 V)
    (ω : ConfigSpace (Sym2 V)) (he : e ∈ G.edgeFinset) :
    edgeProductOff G p e ω * (if ω e then (1 : ℝ) else -1)
      = edgeProduct G p ω * ((coord e ω - p) / (p * (1 - p))) := by
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  have hpne : p ≠ 0 := hp.ne'
  have hp1ne : (1 : ℝ) - p ≠ 0 := hp1'.ne'
  rw [edgeProduct_eq_off G p e ω he]
  unfold coord
  by_cases h : ω e = true
  · rw [if_pos h, if_pos h, if_pos h]
    field_simp
  · rw [if_neg h, if_neg h, if_neg h]
    field_simp
    ring

omit [DecidableEq V] in

lemma sum_coord_sub (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    ∑ e ∈ G.edgeFinset, (coord e ω - p)
      = openEdgeCount G ω - p * (G.edgeFinset.card : ℝ) := by
  rw [Finset.sum_sub_distrib]
  unfold openEdgeCount coord
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]


lemma hasDerivAt_edgeProduct_clean {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun p => edgeProduct G p ω)
      (edgeProduct G p ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
  refine (hasDerivAt_edgeProduct G ω p).congr_deriv ?_
  rw [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [edgeProductOff_term G p hp hp1 e ω he]


lemma hasDerivAt_fkWeight {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (q : ℝ)
    (ω : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun p => fkWeight G p q ω)
      (fkWeight G p q ω * ((∑ e ∈ G.edgeFinset, (coord e ω - p)) / (p * (1 - p)))) p := by
  have h := (hasDerivAt_edgeProduct_clean G hp hp1 ω).mul_const (q ^ numClusters G ω)
  refine h.congr_deriv ?_
  unfold fkWeight
  ring


end FK
end StatMech
