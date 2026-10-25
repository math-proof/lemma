/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CrossingTranslationInvariance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWAspectInduction
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


noncomputable def cti_inducedHom (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 (translateConfig t ω) (rect a b c d)) →g
      (openSubgraphInduce 2 ω (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))) where
  toFun := fun x => ⟨(x : Site 2) + t, (cti_mem_rect_translate a b c d t x).1 x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj] at hxy ⊢
    rw [openSubgraph_adj] at hxy ⊢
    obtain ⟨hadj, hopen⟩ := hxy
    exact ⟨((cti_isOpenEdge_translate t ω x y).1 ⟨hadj, hopen⟩).1,
           ((cti_isOpenEdge_translate t ω x y).1 ⟨hadj, hopen⟩).2⟩


noncomputable def cti_inducedHomInv (a b c d : ℤ) (t : Site 2)
    (ω : ConfigSpace (Sym2 (Site 2))) :
    (openSubgraphInduce 2 ω (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1))) →g
      (openSubgraphInduce 2 (translateConfig t ω) (rect a b c d)) where
  toFun := fun x => ⟨(x : Site 2) - t, by
    rw [cti_mem_rect_translate a b c d t]; simp only [sub_add_cancel]; exact x.2⟩
  map_rel' := by
    intro x y hxy
    rw [openSubgraphInduce_adj] at hxy ⊢
    rw [openSubgraph_adj] at hxy ⊢
    obtain ⟨hadj, hopen⟩ := hxy
    have key := (cti_isOpenEdge_translate t ω ((x : Site 2) - t) ((y : Site 2) - t)).2
    simp only [sub_add_cancel] at key
    exact ⟨(key ⟨hadj, hopen⟩).1, (key ⟨hadj, hopen⟩).2⟩


end Universality
end StatMech
