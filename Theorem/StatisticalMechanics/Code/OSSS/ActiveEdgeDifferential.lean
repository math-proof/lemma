/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/ActiveEdgeDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCovLowerGeom
import Theorem.StatisticalMechanics.Code.OSSS.RussoPrefactor
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace ActiveEdgeDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open RevealmentTranslation

open LindebergTree

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {d : ℕ}

lemma mean_active_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ) (f : ConfigSpace G.edgeSet → ℝ) :
    Lindeberg.mean (FK.activeProb G pf q) f = FK.activeMean G pf q f := by
  unfold Lindeberg.mean FK.activeMean
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma cov_active_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ) (f g : ConfigSpace G.edgeSet → ℝ) :
    Lindeberg.cov (FK.activeProb G pf q) f g = FK.activeCov G pf q f g := by
  unfold Lindeberg.cov FK.activeCov
  rw [mean_active_eq, mean_active_eq, mean_active_eq]


end ActiveEdgeDifferential
end OSSS
end StatMech
