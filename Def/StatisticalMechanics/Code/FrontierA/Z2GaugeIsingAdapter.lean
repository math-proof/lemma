/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeIsingAdapter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDualCoupling
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

noncomputable def gaugeClosedSurfaceFamily (incidence : P → Finset E) :
    Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.filter (IsClosedPlaquetteSet incidence)


noncomputable def gaugeWilsonSurfaceFamily (incidence : P → Finset E)
    (L : Finset E) : Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.filter
    (fun A => HasWilsonBoundary incidence A L)


noncomputable def shiftedDualCutFamily {G : SimpleGraph V}
    [DecidableRel G.Adj] (D : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) :=
  (cutSpace G).image (fun delta => delta ∆ D)


def dualPlaquetteEmbedding {G : SimpleGraph V} [DecidableRel G.Adj]
    (dualEdge : P ≃ G.edgeFinset) : P ↪ Sym2 V where
  toFun p := (dualEdge p).1
  inj' := fun _ _ h => dualEdge.injective (Subtype.ext h)


noncomputable def dualIsingCoupling {G : SimpleGraph V} [DecidableRel G.Adj]
    (dualEdge : P ≃ G.edgeFinset) (K : P → ℝ) (e : Sym2 V) : ℝ :=
  if he : e ∈ G.edgeFinset then gaugeDualCoupling (K (dualEdge.symm ⟨e, he⟩)) else 0

end StatMech.FrontierA
