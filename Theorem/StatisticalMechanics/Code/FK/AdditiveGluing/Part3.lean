/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AdditiveGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTiling.Part2
import Theorem.StatisticalMechanics.Code.FK.GenuineEdgeCollapse
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.FK.AdditiveGluing.Part3
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]


theorem agl_fkZ_translate (d : ℕ) (v : Site d) (f : V → Site d) (g : W → Site d)
    (φ : V ≃ W) (hfg : ∀ x, g (φ x) = f x + v) (p q : ℝ)
    [DecidableRel ((hypercubicLattice d).comap f).Adj]
    [DecidableRel ((hypercubicLattice d).comap g).Adj] :
    fkZ ((hypercubicLattice d).comap f) p q = fkZ ((hypercubicLattice d).comap g) p q :=
  fsm_fkZ_iso _ _ (agl_transBlockIso d v f g φ hfg) p q


end FK
end StatMech
