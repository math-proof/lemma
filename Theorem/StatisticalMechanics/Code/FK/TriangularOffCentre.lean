/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

variable {V : Type*} [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {Sin Sout : Set V} [Fintype Sin] [Fintype Sout]


theorem ocd_comapAdjMatch
    (iota : Sin -> Sout) (hiotaVal : forall x, (iota x : V) = (x : V)) :
    ocd_AdjMatch (SimpleGraph.comap Subtype.val G)
      (SimpleGraph.comap Subtype.val G) iota := by
  intro x y
  rw [SimpleGraph.comap_adj, SimpleGraph.comap_adj, hiotaVal x, hiotaVal y]


theorem ocd_comap_bdryIn_of_outsideGraph_adj
    (iota : Sin -> Sout) (hiotaVal : forall x, (iota x : V) = (x : V))
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : forall x : Sin, ¬ bdryOut (iota x))
    (hbdryIn : forall (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
    (psi : ConfigSpace (Sym2 Sout)) {x : Sin} {z : Sout}
    (h : (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
      iota bdryOut psi).Adj (iota x) z) :
    bdryIn x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hb, _⟩
  · have hznot : (z : V) ∉ Sin := by
      intro hz
      refine hrange ⟨s(x, ⟨(z : V), hz⟩), ?_⟩
      rw [ocd_innerEdge_mk]
      have hzeq : iota ⟨(z : V), hz⟩ = z :=
        Subtype.ext (hiotaVal ⟨(z : V), hz⟩)
      rw [hzeq]
    have hadj' : G.Adj x.1 z.1 := by
      rw [SimpleGraph.comap_adj] at hadj
      rw [hiotaVal x] at hadj
      exact hadj
    exact hbdryIn x z.1 hadj' hznot
  · exact absurd hb (hmargin x)


theorem ocd_comapInducedWiring_le
    (iota : Sin -> Sout) (hiotaVal : forall x, (iota x : V) = (x : V))
    (hiota : Function.Injective iota)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : forall x : Sin, ¬ bdryOut (iota x))
    (hbdryIn : forall (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
    (psi : ConfigSpace (Sym2 Sout)) :
    ocd_inducedWiring (SimpleGraph.comap Subtype.val G) iota bdryOut psi <=
      boundaryCliqueGraph bdryIn := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : iota x ≠ iota y := fun h => hne (hiota h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_comap_bdryIn_of_outsideGraph_adj G iota hiotaVal
        bdryOut bdryIn hmargin hbdryIn psi hadj
  · have hreach' :
        (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
          iota bdryOut psi).Reachable (iota y) (iota x) := hreach.symm
    have hne' : iota y ≠ iota x := fun h => hne (hiota h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_comap_bdryIn_of_outsideGraph_adj G iota hiotaVal
        bdryOut bdryIn hmargin hbdryIn psi hadj


theorem ocd_comapInducedWiring_le_equiv
    (e : V ≃ V) (he : ∀ x y, G.Adj (e x) (e y) ↔ G.Adj x y)
    (iota : Sin -> Sout) (hiotaVal : ∀ x, (iota x : V) = e (x : V))
    (hiota : Function.Injective iota)
    (bdryOut : Sout -> Prop) [DecidablePred bdryOut]
    (bdryIn : Sin -> Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : Sin, ¬ bdryOut (iota x))
    (hbdryIn : ∀ (x : Sin) (z : V), G.Adj x.1 z -> z ∉ Sin -> bdryIn x)
    (psi : ConfigSpace (Sym2 Sout)) :
    ocd_inducedWiring (SimpleGraph.comap Subtype.val G) iota bdryOut psi <=
      boundaryCliqueGraph bdryIn := by
  have hfirst : ∀ (x : Sin) (z : Sout),
      (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
        iota bdryOut psi).Adj (iota x) z -> bdryIn x := by
    intro x z h
    rw [ocd_outsideGraph_adj] at h
    rcases h with ⟨hadj, _, hrange⟩ | ⟨_, hb, _⟩
    · have hznot : e.symm (z : V) ∉ Sin := by
        intro hz
        refine hrange ⟨s(x, ⟨e.symm (z : V), hz⟩), ?_⟩
        rw [ocd_innerEdge_mk]
        have hzeq : iota ⟨e.symm (z : V), hz⟩ = z := by
          apply Subtype.ext
          rw [hiotaVal]
          exact e.apply_symm_apply (z : V)
        rw [hzeq]
      have hadj' : G.Adj x.1 (e.symm (z : V)) := by
        rw [SimpleGraph.comap_adj, hiotaVal x] at hadj
        apply (he x.1 (e.symm (z : V))).mp
        simpa using hadj
      exact hbdryIn x (e.symm (z : V)) hadj' hznot
    · exact absurd hb (hmargin x)
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : iota x ≠ iota y := fun h => hne (hiota h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact hfirst x z hadj
  · have hreach' :
        (ocd_outsideGraph (SimpleGraph.comap Subtype.val G)
          iota bdryOut psi).Reachable (iota y) (iota x) := hreach.symm
    have hne' : iota y ≠ iota x := fun h => hne (hiota h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨z, hadj, _⟩
    · exact absurd heq hne'
    · exact hfirst y z hadj

end
end StatMech.FK
