/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Def.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part10
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section LatticeBridge

open StatMech.Lattice


@[simp] theorem latticeSide_eq_true {S : Set (Site 2)} {x : Site 2} :
    latticeSide S x = true ↔ x ∈ S := by
  unfold latticeSide
  exact @decide_eq_true_iff (x ∈ S) (Classical.propDecidable _)


theorem crossCount_even_iff_latticeSide (S : Set (Site 2)) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    Even (crossCount S w) ↔ latticeSide S x = latticeSide S y := by
  rw [crossCount_parity S w]
  constructor
  · intro hiff
    by_cases hx : x ∈ S
    · rw [(latticeSide_eq_true).mpr hx, (latticeSide_eq_true).mpr (hiff.mp hx)]
    · have hy : y ∉ S := fun hy => hx (hiff.mpr hy)
      have e1 : latticeSide S x = false := by
        cases h : latticeSide S x with
        | false => rfl
        | true => exact absurd ((latticeSide_eq_true).mp h) hx
      have e2 : latticeSide S y = false := by
        cases h : latticeSide S y with
        | false => rfl
        | true => exact absurd ((latticeSide_eq_true).mp h) hy
      rw [e1, e2]
  · intro hcol
    constructor
    · intro hx
      have : latticeSide S x = true := (latticeSide_eq_true).mpr hx
      rw [hcol] at this
      exact (latticeSide_eq_true).mp this
    · intro hy
      have : latticeSide S y = true := (latticeSide_eq_true).mpr hy
      rw [← hcol] at this
      exact (latticeSide_eq_true).mp this


theorem latticeRegionBoundary_evenOnLoop (S : Set (Site 2)) {x : Site 2}
    (w : (hypercubicLattice 2).Walk x x) : Even (crossCount S w) :=
  (crossCount_even_iff_latticeSide S w).mpr rfl


theorem latticeSide_isRegion_of_pullback_eq_bdEdge
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (ψ : Sym2 (Site 2) ≃ Sym2 (Site 2))
    (S : Set (Site 2)) {w : Site 2} (W : Gd.Walk w w)
    (hpull : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ bdEdge S s(u, v))) :
    ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      (s(u, v) ∈ (W.edges.toFinset).image ψ.symm ↔ latticeSide S u ≠ latticeSide S v) := by
  intro u v h
  rw [hpull h, bdEdge_mk]
  
  have hu : u ∈ S ↔ latticeSide S u = true := (latticeSide_eq_true).symm
  have hv : v ∈ S ↔ latticeSide S v = true := (latticeSide_eq_true).symm
  rw [hu, hv]
  cases latticeSide S u <;> cases latticeSide S v <;> simp

end LatticeBridge


section UnconditionalCapstone

variable {V : Type} [Fintype V] [DecidableEq V]
  {Gp Gd : SimpleGraph V} [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


theorem even_to_cut_of_boundsRegion' [Nonempty V] (hG : Gp.Preconnected)
    (ψ : Sym2 V ≃ Sym2 V)
    (hsymm : ∀ e ∈ Gd.edgeFinset, ψ.symm e ∈ Gp.edgeFinset)
    (hreg : DualWalkBoundsRegion Gp Gd ψ) :
    ∀ F ∈ evenSubgraphs Gd, (F.image ψ.symm) ∈ cutSpace Gp :=
  even_to_cut_of_boundsRegion hG ψ hsymm (evenSubgraphWalkDecomp_general Gd) hreg


end UnconditionalCapstone
end Ising
end StatMech
