/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part3
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

theorem separated_finiteGraph_eq_bot :
    separatedSymmetricDomain.finiteGraph = ⊥ := by
  ext x y
  constructor
  · intro hxy
    have hx : (x.1 : Site 2) = separatedSiteOne ∨
        (x.1 : Site 2) = separatedSiteTwo := by
      have hxmem := x.2
      change x.1 ∈ ({separatedSiteOne, separatedSiteTwo} : Set (Site 2)) at hxmem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem
    have hy : (y.1 : Site 2) = separatedSiteOne ∨
        (y.1 : Site 2) = separatedSiteTwo := by
      have hymem := y.2
      change y.1 ∈ ({separatedSiteOne, separatedSiteTwo} : Set (Site 2)) at hymem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hymem
    change (hypercubicLattice 2).Adj x.1 y.1 at hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      rw [hx, hy, hypercubicLattice_adj, Fin.sum_univ_two] at hxy <;>
      norm_num [separatedSiteOne, separatedSiteTwo] at hxy
  · simp


theorem separated_not_openConnected
    (omega : ConfigSpace (Sym2 separatedSymmetricDomain.Vertex)) :
    ¬separatedSymmetricDomain.OpenConnected omega := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hxval : (x.1 : Site 2) = separatedSiteOne := by
    simpa [OnGammaOne, separatedSymmetricDomain] using hx
  have hyval : (y.1 : Site 2) = separatedSiteTwo := by
    simpa [OnGammaTwo, separatedSymmetricDomain] using hy
  have hbot : (FK.openSub separatedSymmetricDomain.finiteGraph omega) = ⊥ := by
    rw [separated_finiteGraph_eq_bot]
    ext u v
    simp [FK.openSub]
  rw [hbot] at hxy
  have hxyEq : x = y := by simpa using hxy
  have hval := congrArg Subtype.val hxyEq
  rw [hxval, hyval] at hval
  norm_num [separatedSiteOne, separatedSiteTwo] at hval


theorem separated_not_mixedConnected
    (omega : ConfigSpace (Sym2 separatedSymmetricDomain.Vertex)) :
    ¬separatedSymmetricDomain.MixedConnected omega := by
  rw [mixedConnected_iff_openConnected]
  exact separated_not_openConnected omega


theorem separated_openConnectionProbability_eq_zero (q : Real) :
    separatedSymmetricDomain.openConnectionProbability q = 0 := by
  unfold openConnectionProbability
  apply Finset.sum_eq_zero
  intro omega _
  simp [separated_not_openConnected omega]


theorem separated_selfDuality_lower_bound_false :
    ¬(1 / (1 + (1 : Real) ^ 2) ≤
      separatedSymmetricDomain.openConnectionProbability 1) := by
  rw [separated_openConnectionProbability_eq_zero]
  norm_num


theorem separated_mixedDualComplementRN_isEmpty (q : Real) :
    IsEmpty (MixedDualComplementRN separatedSymmetricDomain q) :=
  mixedDualComplementRN_isEmpty_of_all_disconnected
    separatedSymmetricDomain q separated_not_mixedConnected


end
end SymmetricDomain
end BeffaraDC
end StatMech
