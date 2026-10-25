/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/MixedCurrentTraceFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.MixedCurrentTraceMixing.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceZeroBeta
open MeasureTheory Set


namespace StatMech.FrontierB

open ConfigSpace StatMech.FK Lattice Percolation

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]

def pairOrSupport [DecidableEq E] (S : Finset E) : Finset (E ⊕ E) :=
  S.image Sum.inl ∪ S.image Sum.inr

def pairOrLocalPattern [DecidableEq E] (S : Finset E)
    (a : ↑(pairOrSupport S) -> Bool) : ↑S -> Bool := fun e =>
  a ⟨Sum.inl e.1, Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)⟩ ||
  a ⟨Sum.inr e.1, Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨e.1, e.2, rfl⟩)⟩

def pairOrPullbackPatternSet [DecidableEq E] (S : Finset E)
    (A : Set (↑S -> Bool)) : Set (↑(pairOrSupport S) -> Bool) :=
  {a | pairOrLocalPattern S a ∈ A}

end StatMech.FrontierB
