/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part7
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


open MeasureTheory Filter

noncomputable def intervalPatternRestriction (r : ℕ) (t : Finset (Site 1))
    (ht : (t : Set (Site 1)) ⊆ box 1 r) (p : Fin (2 * r + 1) → Fin 2) : t → Bool :=
  fun x => boolEquivFin2.symm
    (p (box1EquivFin r ⟨x.1, ht x.2⟩))

end StatMech.FrontierB
