/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part6
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


noncomputable def abigInternalEdgeEquiv [DecidableEq W] (T : Finset W) :
    Sym2 T ≃ abigInternalEdges T :=
  Equiv.ofBijective
    (fun e => ⟨Sym2.map (Subtype.val : T -> W) e, by
      induction e using Sym2.inductionOn with
      | _ x y =>
          rw [Sym2.map_mk]
          exact (mem_abigInternalEdges).2
            ⟨x, x.property, y, y.property, rfl⟩⟩)
    ⟨by
      intro e f hef
      apply Sym2.map.injective Subtype.val_injective
      exact congrArg Subtype.val hef,
    by
      rintro ⟨e, he⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_abigInternalEdges).1 he
      refine ⟨s((⟨x, hx⟩ : T), (⟨y, hy⟩ : T)), ?_⟩
      apply Subtype.ext
      change Sym2.map (Subtype.val : T -> W)
        s((⟨x, hx⟩ : T), (⟨y, hy⟩ : T)) = s(x, y)
      rw [Sym2.map_mk]⟩

end Sharpness
end StatMech
