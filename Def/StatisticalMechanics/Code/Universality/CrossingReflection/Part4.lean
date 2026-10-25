/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part3
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


noncomputable def crf_inducedHom (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 ω (rect a b c d)) →g
      (openSubgraphInduce 2 (crf_swapConfig ω) (rect c d a b)) where
  toFun := fun x => ⟨crf_swap (x : Site 2), (crf_mem_rect_swap a b c d x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    obtain ⟨hadj, hopen⟩ := hxy
    show IsOpenEdge 2 (crf_swapConfig ω) (crf_swap (x : Site 2)) (crf_swap (y : Site 2))
    rw [crf_isOpenEdge_swap ω (crf_swap (x : Site 2)) (crf_swap (y : Site 2))]
    simp only [crf_swap_involutive]
    exact ⟨hadj, hopen⟩


noncomputable def crf_inducedHomInv (a b c d : ℤ) (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (crf_swapConfig ω) (rect c d a b)) →g
      (openSubgraphInduce 2 ω (rect a b c d)) where
  toFun := fun x => ⟨crf_swap (x : Site 2), (crf_mem_rect_swap c d a b x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hxy
    obtain ⟨hadj, hopen⟩ := hxy
    show IsOpenEdge 2 ω (crf_swap (x : Site 2)) (crf_swap (y : Site 2))
    exact (crf_isOpenEdge_swap ω (x : Site 2) (y : Site 2)).1 ⟨hadj, hopen⟩


end Universality
end StatMech
