/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryPhi.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryProfile.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part13
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Mathlib.Data.Finset.Preimage
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


theorem abb_probV_eq_section {E : Type*} [Fintype E] [DecidableEq E]
    (p : E → Real) (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : StatMech.DependsOn A (F : Set E)) :
    probV p A = probV (fun e : F ↦ p e)
      (ih_section A F) := by
  let mu := inhomBernoulliProductMeasure (fun e ↦ (p e).toNNReal)
    (fun e ↦ Real.toNNReal_le_one.mpr (hp1 e))
  have hAcyl : A = MeasureTheory.cylinder F (ih_section A F) :=
    ih_eq_cylinder_of_dependsOn F hA
  calc
    probV p A = mu.real A :=
      (inhom_real_eq_probV_of_mem p hp0 hp1 A).symm
    _ = mu.real (MeasureTheory.cylinder F (ih_section A F)) :=
      congrArg mu.real hAcyl
    _ = (inhomBernoulliProductMeasure
          (fun e : F ↦ (p e).toNNReal)
          (fun e ↦ Real.toNNReal_le_one.mpr (hp1 e))).real
          (ih_section A F) :=
      inhom_realProb_cylinder (fun e ↦ (p e).toNNReal)
        (fun e ↦ Real.toNNReal_le_one.mpr (hp1 e)) F _
    _ = probV (fun e : F ↦ p e) (ih_section A F) :=
      inhom_real_eq_probV_of_mem (fun e : F ↦ p e)
        (fun e ↦ hp0 e) (fun e ↦ hp1 e) _


theorem abb_probV_eq_of_agreeOn {E : Type*} [Fintype E] [DecidableEq E]
    (p q : E → Real)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (A : Set (ConfigSpace E)) (F : Finset E)
    (hA : StatMech.DependsOn A (F : Set E))
    (hpq : ∀ e ∈ F, p e = q e) :
    probV p A = probV q A := by
  rw [abb_probV_eq_section p hp0 hp1 A F hA,
    abb_probV_eq_section q hq0 hq1 A F hA]
  congr 1
  funext e
  exact hpq e e.property


theorem abb_internal_openSub_adj {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) (T : Finset W)
    (eta : ConfigSpace (abigInternalEdges T)) (a b : T) :
    (openSub (G.induce (T : Set W))
      (cfgEquiv (abigInternalEdgeEquiv T) eta)).Adj a b ↔
      (openSub G (ih_fill (abigInternalEdges T) eta)).Adj (a : W) (b : W) := by
  have he : s((a : W), (b : W)) ∈ abigInternalEdges T :=
    mem_abigInternalEdges.mpr ⟨a, a.property, b, b.property, rfl⟩
  have hcoord : abigInternalEdgeEquiv T s(a, b) =
      (⟨s((a : W), (b : W)), he⟩ : abigInternalEdges T) := by
    apply Subtype.ext
    exact abigInternalEdgeEquiv_mk T a b
  simp only [openSub, SimpleGraph.induce_adj, cfgEquiv_apply]
  rw [ih_fill, dif_pos he]
  constructor
  · rintro ⟨hG, heta⟩
    exact ⟨hG, hcoord ▸ heta⟩
  · rintro ⟨hG, heta⟩
    exact ⟨hG, hcoord.symm ▸ heta⟩


theorem abb_preimage_connEvent_induce {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) (T : Finset W) (o x : T) :
    (cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹'
        connEvent (G.induce (T : Set W)) Set.univ o {x} =
      ih_section (connEvent G (T : Set W) (o : W) {(x : W)})
        (abigInternalEdges T) := by
  ext eta
  change ConnToSet (G.induce (T : Set W))
      (cfgEquiv (abigInternalEdgeEquiv T) eta) Set.univ o {x} ↔
    ConnToSet G (ih_fill (abigInternalEdges T) eta)
      (T : Set W) (o : W) {(x : W)}
  constructor
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    let f :
        ((openSub (G.induce (T : Set W))
          (cfgEquiv (abigInternalEdgeEquiv T) eta)).induce Set.univ) →g
        ((openSub G (ih_fill (abigInternalEdges T) eta)).induce
          (T : Set W)) :=
      { toFun := fun z ↦ ⟨(z : T), z.1.property⟩
        map_rel' := fun {u v} huv ↦
          (abb_internal_openSub_adj G T eta u v).mp huv }
    exact ⟨o.property, (x : W), x.property, rfl, hconn.map f⟩
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = (x : W) := Set.mem_singleton_iff.mp hy
    subst y
    let f :
        ((openSub G (ih_fill (abigInternalEdges T) eta)).induce
          (T : Set W)) →g
        ((openSub (G.induce (T : Set W))
          (cfgEquiv (abigInternalEdgeEquiv T) eta)).induce Set.univ) :=
      { toFun := fun z ↦ ⟨(z : T), Set.mem_univ _⟩
        map_rel' := fun {u v} huv ↦
          (abb_internal_openSub_adj G T eta u v).mpr huv }
    exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl, hconn.map f⟩


theorem abb_probV_connEvent_eq_induce {W : Type*}
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (p : Sym2 W → Real)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (T : Finset W) (o x : T) :
    probV p (connEvent G (T : Set W) (o : W) {(x : W)}) =
      probV (fun e : Sym2 T ↦ p (Sym2.map Subtype.val e))
        (connEvent (G.induce (T : Set W)) Set.univ o {x}) := by
  let F := abigInternalEdges T
  let A := connEvent G (T : Set W) (o : W) {(x : W)}
  let AI := connEvent (G.induce (T : Set W)) Set.univ o {x}
  let q : Sym2 T → Real := fun e ↦ p (Sym2.map Subtype.val e)
  have hdep : StatMech.DependsOn A (F : Set (Sym2 W)) :=
    abig_connEvent_dependsOn G T (o : W) (x : W)
  rw [abb_probV_eq_section p hp0 hp1 A F hdep]
  symm
  calc
    probV q AI =
        probV (fun y : F ↦ q ((abigInternalEdgeEquiv T).symm y))
          ((cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹' AI) :=
      abfs_probV_transfer (abigInternalEdgeEquiv T) q AI
    _ = probV (fun e : F ↦ p e) (ih_section A F) := by
      have hevent :
          (cfgEquiv (abigInternalEdgeEquiv T)) ⁻¹' AI = ih_section A F := by
        exact abb_preimage_connEvent_induce G T o x
      rw [hevent]
      congr 1
      funext e
      apply congrArg p
      exact congrArg Subtype.val ((abigInternalEdgeEquiv T).apply_symm_apply e)


theorem abb_hom_real_eq_probV {E : Type*} [Fintype E] [DecidableEq E]
    (p : NNReal) (hp : p ≤ 1) (A : Set (ConfigSpace E)) :
    (inhomBernoulliProductMeasure (fun _ : E ↦ p) (fun _ ↦ hp)).real A =
      probV (fun _ : E ↦ (p : Real)) A := by
  simpa using
    (inhom_real_eq_probV_of_mem (fun _ : E ↦ (p : Real))
      (fun _ ↦ p.coe_nonneg) (fun _ ↦ NNReal.coe_le_one.mpr hp) A)


theorem abb_probV_section_const_eq_induce {W : Type*} [DecidableEq W]
    (p : Real) (G : SimpleGraph W) (T : Finset W) (o x : T) :
    probV (fun _ : abigInternalEdges T ↦ p)
        (ih_section (connEvent G (T : Set W) (o : W) {(x : W)})
          (abigInternalEdges T)) =
      probV (fun _ : Sym2 T ↦ p)
        (connEvent (G.induce (T : Set W)) Set.univ o {x}) := by
  have ht := abfs_probV_transfer (abigInternalEdgeEquiv T)
    (fun _ : Sym2 T ↦ p)
    (connEvent (G.induce (T : Set W)) Set.univ o {x})
  rw [abb_preimage_connEvent_induce G T o x] at ht
  simpa only using ht.symm


end Sharpness
end StatMech
