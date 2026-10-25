/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
import Mathlib.Probability.Distributions.Uniform
set_option maxHeartbeats 800000

open Finset Real


namespace ShannonEntropy

/-- The support of a PMF on a finite type, returned as a `Finset`: the set of
elements $s$ with $p(s) \neq 0$. -/
noncomputable def supportFinset {S : Type*} [Fintype S] (p : PMF S) : Finset S :=
  Finset.univ.filter (fun s => p s ≠ 0)

end ShannonEntropy
