/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/FrameChangeIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Universality.G3PercDualityFull.Part2
import Def.StatisticalMechanics.Code.Universality.FrameChangeIso.Part5
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem fci_sharedEdgeMap_injective : Function.Injective fci_sharedEdgeMap := by
  intro e e' heq
  apply Subtype.ext
  obtain ⟨f, g, hval⟩ := fci_sym2_exists e.1
  obtain ⟨f', g', hval'⟩ := fci_sym2_exists e'.1
  have hfg : (hypercubicLattice 2).Adj f g :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  have hfg' : (hypercubicLattice 2).Adj f' g' :=
    (SimpleGraph.mem_edgeSet _).mp (hval' ▸ e'.2)
  have hshared : sharedPrimalEdge f g = sharedPrimalEdge f' g' := by
    have heq' := congrArg Subtype.val heq
    change fci_sharedEdgeRaw e.1 = fci_sharedEdgeRaw e'.1 at heq'
    rwa [hval, hval', fci_sharedEdgeRaw_mk_of_adj hfg,
      fci_sharedEdgeRaw_mk_of_adj hfg'] at heq'
  rw [hval, hval']
  exact (jce_sharedPrimalEdge_inj hfg hfg').mpr hshared

theorem fci_sharedEdgeMap_surjective : Function.Surjective fci_sharedEdgeMap := by
  intro e
  obtain ⟨p, q, hval⟩ := fci_sym2_exists e.1
  have hpq : (hypercubicLattice 2).Adj p q :=
    (SimpleGraph.mem_edgeSet _).mp (hval ▸ e.2)
  obtain ⟨f, g, hfg, hshared⟩ := jfc_flankingFaces hpq
  let d : (hypercubicLattice 2).edgeSet :=
    ⟨s(f, g), (SimpleGraph.mem_edgeSet _).mpr hfg⟩
  refine ⟨d, Subtype.ext ?_⟩
  change fci_sharedEdgeRaw s(f, g) = e.1
  rw [fci_sharedEdgeRaw_mk_of_adj hfg, hshared, ← hval]


end Universality
end StatMech
