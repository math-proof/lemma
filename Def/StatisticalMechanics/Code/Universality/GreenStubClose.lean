module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
public import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part6
public import Theorem.StatisticalMechanics.Code.Universality.GreenStubClose
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

def gst_greenToNegHom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (openSubgraphInduce 2 (gec2_greenConfig ω n) (rect 0 (n + 1) 0 n)) →g
      (openSubgraphInduce 2 (des_negConfig ω) (rect 0 (n + 1) 0 n)) where
  toFun := id
  map_rel' := by
    intro x y h
    rw [openSubgraphInduce_adj, openSubgraph_adj] at h ⊢
    obtain ⟨hadj, hopen⟩ := h
    exact ⟨hadj, by rwa [gst_greenConfig_eq_negConfig_in_box ω n x.2 y.2] at hopen⟩


end Universality
end StatMech
