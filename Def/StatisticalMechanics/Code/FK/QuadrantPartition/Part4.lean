/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Instance.StatisticalMechanics.Code.FK.QuadrantPartition.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


noncomputable def qp_straddleEdges (P : U → Prop) [DecidablePred P] : Finset (Sym2 U) :=
  K₀.edgeFinset.filter (qp_straddleP P)


noncomputable def qp_comapComapIso {V W X : Type*} (g : W → U) (f : V → W) (h : X → U)
    (hgf : Function.Injective (g ∘ f)) (hh : Function.Injective h)
    (hr : Set.range (g ∘ f) = Set.range h) :
    (K₀.comap g).comap f ≃g K₀.comap h where
  toEquiv := (Equiv.ofInjective (g ∘ f) hgf).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective h hh).symm)
  map_rel_iff' := by
    intro a b; simp only [comap_adj, Equiv.trans_apply]
    have key : ∀ z : V,
        h ((Equiv.ofInjective h hh).symm ((Equiv.setCongr hr) ((Equiv.ofInjective (g ∘ f) hgf) z)))
          = g (f z) := fun z => by rw [Equiv.apply_ofInjective_symm hh]; rfl
    rw [key a, key b]


end Peel
end FK
end StatMech
