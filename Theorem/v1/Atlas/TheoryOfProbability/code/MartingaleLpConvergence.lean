/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/MartingaleLpConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TheoryOfProbability.code.MartingaleConvergence
import Theorem.v1.Atlas.TheoryOfProbability.code.UnifIntegrableLp
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

/--
Auxiliary lemma: if a submartingale `f` on a probability space has
`L^p`-norms uniformly bounded by `R` for some `1 < p < ∞`, then the family
`f` is `L^p`-uniformly integrable. Used in the proof of the `L^p` martingale
convergence theorem (Lecture 28).
-/


noncomputable section

end
