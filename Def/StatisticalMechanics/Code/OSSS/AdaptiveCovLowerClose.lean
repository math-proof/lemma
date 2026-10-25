/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FamilyEqzzzResolution
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentSum
open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false


namespace StatMech

namespace OSSS

namespace AdaptiveCovLowerClose

open StatMech.OSSS

open StatMech.OSSS.LindebergTree

open StatMech.OSSS.Lindeberg

open StatMech.OSSS.FrontierFamilyClose

open StatMech.OSSS.FamilyEqzzzResolution

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

open DecisionTree

open scoped Classical

variable {d : ℕ}

variable {W : Type*} [Fintype W] [DecidableEq W]


noncomputable def crossInd (edge : Sym2 W → Sym2 (Site d)) (o : Site d) (n : ℕ) :
    ConfigSpace (Sym2 W) → ℝ :=
  (crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))


noncomputable def boxReveal (μ : ConfigSpace (Sym2 W) → ℝ)
    (edge : Sym2 W → Sym2 (Site d)) (endU endV : Sym2 W → Site d)
    (k : ℕ) (e : Sym2 W) : ℝ :=
  Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                then (1 : ℝ) else 0)
    + Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0)


end AdaptiveCovLowerClose
end OSSS
end StatMech
