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
import Def.StatisticalMechanics.Code.Sharpness.ABBoundaryPhi
open Filter Finset Set SimpleGraph Topology
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice

open StatMech.Percolation


@[simp] theorem abbEdgeEquiv_mk {V U : Type*} (sigma : V ≃ U)
    (x y : V) :
    abbEdgeEquiv sigma s(x, y) = s(sigma x, sigma y) := by
  simp [abbEdgeEquiv, StatMech.Lattice.sym2Congr_mk]


theorem abb_openSub_adj_relabel {V U : Type*}
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (omega : ConfigSpace (Sym2 U)) (x y : V) :
    (openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).Adj x y ↔
      (openSub H omega).Adj (sigma x) (sigma y) := by
  simp only [openSub, cfgEquiv_apply, abbEdgeEquiv_mk]
  exact and_congr (hG x y) Iff.rfl


theorem abb_connWithin_univ_relabel {V U : Type*}
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (omega : ConfigSpace (Sym2 U)) (x y : V) :
    ConnWithin G (cfgEquiv (abbEdgeEquiv sigma) omega) Set.univ
        ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ ↔
      ConnWithin H omega Set.univ
        ⟨sigma x, Set.mem_univ _⟩ ⟨sigma y, Set.mem_univ _⟩ := by
  constructor
  · intro hconn
    let f :
        ((openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).induce
          Set.univ) →g
        ((openSub H omega).induce Set.univ) :=
      { toFun := fun z ↦ ⟨sigma z, Set.mem_univ _⟩
        map_rel' := fun {a b} hab ↦
          (abb_openSub_adj_relabel G H sigma hG omega a b).mp hab }
    exact hconn.map f
  · intro hconn
    let f :
        ((openSub H omega).induce Set.univ) →g
        ((openSub G (cfgEquiv (abbEdgeEquiv sigma) omega)).induce
          Set.univ) :=
      { toFun := fun z ↦ ⟨sigma.symm z, Set.mem_univ _⟩
        map_rel' := fun {a b} hab ↦ by
          apply (abb_openSub_adj_relabel G H sigma hG omega
            (sigma.symm a) (sigma.symm b)).mpr
          simpa using hab }
    convert hconn.map f using 1 <;> simp [f]


theorem abb_preimage_connEvent_relabel {V U : Type*}
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (o x : V) :
    (cfgEquiv (abbEdgeEquiv sigma)) ⁻¹'
        connEvent G Set.univ o {x} =
      connEvent H Set.univ (sigma o) {sigma x} := by
  ext omega
  change ConnToSet G (cfgEquiv (abbEdgeEquiv sigma) omega)
      Set.univ o {x} ↔ ConnToSet H omega Set.univ (sigma o) {sigma x}
  constructor
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨Set.mem_univ _, sigma x, Set.mem_univ _, rfl,
      (abb_connWithin_univ_relabel G H sigma hG omega o x).mp hconn⟩
  · rintro ⟨_, y, _, hy, hconn⟩
    have hyx : y = sigma x := Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl,
      (abb_connWithin_univ_relabel G H sigma hG omega o x).mpr hconn⟩


theorem abb_probV_connEvent_relabel {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (G : SimpleGraph V) (H : SimpleGraph U) (sigma : V ≃ U)
    (hG : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (p : Sym2 V → Real) (o x : V) :
    probV p (connEvent G Set.univ o {x}) =
      probV (fun e : Sym2 U ↦ p ((abbEdgeEquiv sigma).symm e))
        (connEvent H Set.univ (sigma o) {sigma x}) := by
  rw [← abb_preimage_connEvent_relabel G H sigma hG o x]
  exact abfs_probV_transfer (abbEdgeEquiv sigma) p _


theorem abb_connEvent_univ_dependsOn_edges {V : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (D : Finset (Sym2 V))
    (hD : ∀ a b, G.Adj a b → s(a, b) ∈ D) (o x : V) :
    StatMech.DependsOn (connEvent G Set.univ o {x})
      (D : Set (Sym2 V)) := by
  intro omega omega' hagree
  have hforward : ∀ {eta eta' : ConfigSpace (Sym2 V)},
      (∀ e ∈ D, eta' e = eta e) →
      eta ∈ connEvent G Set.univ o {x} →
      eta' ∈ connEvent G Set.univ o {x} := by
    intro eta eta' heq hconn
    rcases hconn with ⟨_, y, _, hy, hreach⟩
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    let f : ((openSub G eta).induce Set.univ) →g
        ((openSub G eta').induce Set.univ) :=
      { toFun := fun z ↦ ⟨(z : V), Set.mem_univ _⟩
        map_rel' := fun {a b} hab ↦ by
          refine ⟨hab.1, ?_⟩
          have hopen : eta' s((a : V), (b : V)) = true := by
            rw [heq s((a : V), (b : V))
              (hD (a : V) (b : V) hab.1)]
            exact hab.2
          simpa using hopen }
    exact ⟨Set.mem_univ _, x, Set.mem_univ _, rfl, hreach.map f⟩
  constructor
  · exact hforward hagree
  · exact hforward (fun e he ↦ (hagree e he).symm)


end Sharpness
end StatMech
