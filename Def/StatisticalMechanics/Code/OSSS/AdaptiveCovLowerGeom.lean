/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCovLowerGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCovLowerClose
import Theorem.StatisticalMechanics.Code.OSSS.RevealmentTranslation
open scoped BigOperators
open Finset Set


namespace StatMech

namespace OSSS

namespace AdaptiveCovLowerGeom

open Lattice Monotonic RevealmentConstruction AdaptiveCovLowerClose

open RevealmentTranslation

open MonotonicFK

open LindebergTree FamilyEqzzzResolution FrontierFamilyClose DecisionTree

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {d : ℕ}


noncomputable def crossIndG (edge : E → Sym2 (Site d)) (o : Site d) (n : ℕ) :
    ConfigSpace E → ℝ :=
  (crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))


noncomputable def boxRevealG (μ : ConfigSpace E → ℝ)
    (edge : E → Sym2 (Site d)) (endU endV : E → Site d)
    (k : ℕ) (e : E) : ℝ :=
  Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                then (1 : ℝ) else 0)
    + Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0)


end AdaptiveCovLowerGeom
end OSSS
end StatMech
