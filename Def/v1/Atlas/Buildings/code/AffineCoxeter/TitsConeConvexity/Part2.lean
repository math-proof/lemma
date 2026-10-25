/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.WordSigmaInvariance
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.PosOfAscentProof
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Set.Finite.List
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The wall parameter $t_0 = \min_{s \in \mathrm{neg\_set}} \frac{x_s}{x_s - \mu_s}$:
the smallest $t \in [0,1]$ for which the convex combination $(1-t)x + t\mu$ reaches
the wall $\{z : z_s = 0\}$ for some $s$. -/
noncomputable def wallParam (x μ : B → ℝ) (neg_set : Finset B)
    (hne : neg_set.Nonempty) (hx : ∀ s, x s ≥ 0) (hμ : ∀ s ∈ neg_set, μ s < 0) : ℝ :=
  (neg_set.image (fun s => x s / (x s - μ s))).min' (hne.image _)

end TitsCone
