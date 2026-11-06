/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TheoryOfProbability.code.FiniteMarkovChain
import Structure.v1.Atlas.TheoryOfProbability.code.KolmogorovCycle.Part2
open MeasureTheory ProbabilityTheory Finset BigOperators


namespace StochasticMatrix

variable {M : ℕ}

/-- `NNReal`-valued version of `pathProduct`: the product of forward transition probabilities
along the path, packaged as a nonnegative real. -/
noncomputable def listPathProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → NNReal
  | [] => 1
  | [_] => 1
  | a :: b :: rest => ⟨P.prob a b, P.nonneg a b⟩ * listPathProduct P (b :: rest)

/-- The product of ratios `P(xᵢ, xᵢ₊₁) / P(xᵢ₊₁, xᵢ)` along a path. This is the quantity
that defines the "cycle weight" used to construct a reversible measure from Kolmogorov's
cycle condition. -/
noncomputable def listRatioProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → NNReal
  | [] => 1
  | [_] => 1
  | a :: b :: rest =>
    (⟨P.prob a b, P.nonneg a b⟩ / ⟨P.prob b a, P.nonneg b a⟩) * listRatioProduct P (b :: rest)

/-- The **cycle weight** of state `j` relative to a reference state `i₀`: defined as the
`listRatioProduct` along some (classically chosen) positive-probability path from `i₀` to `j`.
For chains satisfying Kolmogorov's cycle condition this value is path-independent
(`cycleWeight_path_independent`) and yields the unique-up-to-scaling reversible measure. -/
noncomputable def cycleWeight (P : StochasticMatrix M) (hirr : P.IsIrreducible)
    (i₀ : Fin (M + 1)) (j : Fin (M + 1)) : NNReal :=
  listRatioProduct P (Classical.choose (hirr.exists_path i₀ j))

end StochasticMatrix
