/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Instance.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part15
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorOuterDualEdge_ne_diag {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma'))
    (x : RlcConnectorOuterDualVertex gamma gamma') :
    rlc_connectorOuterDualEdge gamma gamma' f ≠ s(x, x) := by
  unfold rlc_connectorOuterDualEdge
  split
  · rename_i hf
    have hedge := hf.choose.2
    revert hedge
    induction hf.choose.1 using Sym2.inductionOn with
    | _ u v =>
        intro hedge heq
        rw [SimpleGraph.mem_edgeSet] at hedge
        rw [Sym2.map_mk, Sym2.eq_iff] at heq
        rcases heq with h | h
        · apply hedge.ne
          exact rlc_connectorOuterTargetVertex_injective gamma gamma'
            (h.1.trans h.2.symm)
        · apply hedge.ne
          exact rlc_connectorOuterTargetVertex_injective gamma gamma'
            (h.2.trans h.1.symm).symm
  · intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with h | h
    · have hbool : false = true := congrArg
        (fun z => match z with
          | Sum.inr (Sum.inl (_, side)) => side
          | _ => false) (h.1.trans h.2.symm)
      simp at hbool
    · have hbool : false = true := congrArg
        (fun z => match z with
          | Sum.inr (Sum.inl (_, side)) => side
          | _ => false) (h.1.trans h.2.symm)
      simp at hbool


theorem rlc_connectorOuterDualEdge_mem_random {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (f : Ising.kwg_Edge
      (rlc_connectorAugmentedPlanarDomain gamma gamma')) :
    rlc_connectorOuterDualEdge gamma gamma' f ∈
      (rlc_connectorOuterRandomGraph gamma gamma').edgeSet := by
  induction hxy : rlc_connectorOuterDualEdge gamma gamma' f using
      Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      refine ⟨?_, f, hxy⟩
      intro h
      subst y
      exact rlc_connectorOuterDualEdge_ne_diag gamma gamma' f x hxy


theorem rlc_connectorOuterRandom_edgeFinset {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorOuterRandomGraph gamma gamma').edgeFinset =
      Finset.univ.image (rlc_connectorOuterDualEdge gamma gamma') := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, Finset.mem_image]
  constructor
  · intro he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeSet] at he
        exact ⟨he.2.choose, Finset.mem_univ _, he.2.choose_spec⟩
  · rintro ⟨f, _, rfl⟩
    exact rlc_connectorOuterDualEdge_mem_random gamma gamma' f


theorem rlc_pimsEdgeEquiv_mem_latticeEdge {e : Sym2 (Site 2)}
    (he : e ∈ (hypercubicLattice 2).edgeSet) :
    rlc_pimsEdgeEquiv e ∈ (hypercubicLattice 2).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet] at he
      have hinv : (hypercubicLattice 2).Adj
          (rlc_dualReflect.symm x) (rlc_dualReflect.symm y) := by
        rw [rlc_adj_dualReflect]
        simpa using he
      rw [rlc_pimsEdgeEquiv_apply, Sym2.map_mk]
      obtain ⟨u, v, huv, hadj⟩ := sharedPrimalEdge_isLatticeEdge hinv
      rw [fci_faceEdgeEquiv_mk_of_adj hinv, huv]
      exact (SimpleGraph.mem_edgeSet _).mpr hadj


end
end StatMech.Universality
