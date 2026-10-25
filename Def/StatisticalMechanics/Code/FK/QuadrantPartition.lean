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


noncomputable def qp_comapIsoOfRangeEq {V W : Type*} (f : V → U) (g : W → U)
    (hf : Function.Injective f) (hg : Function.Injective g) (hr : Set.range f = Set.range g) :
    K₀.comap f ≃g K₀.comap g where
  toEquiv :=
    (Equiv.ofInjective f hf).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective g hg).symm)
  map_rel_iff' := by
    intro a b
    simp only [comap_adj, Equiv.trans_apply]
    have key : ∀ z : V,
        g ((Equiv.ofInjective g hg).symm ((Equiv.setCongr hr) ((Equiv.ofInjective f hf) z))) = f z :=
      fun z => by rw [Equiv.apply_ofInjective_symm hg]; rfl
    rw [key a, key b]


end FK
end StatMech
