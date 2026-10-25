/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyLocalLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.LLLRandomVariableModel
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound
set_option maxHeartbeats 1600000

/-- Application of the random-variable Lovász Local Lemma to the symmetric Ramsey
problem: if $e \cdot 2^{1 - \binom{k}{2}} \cdot (\binom{k}{2}\binom{n}{k-2} + 1) \le 1$,
there exists a graph on $n$ vertices with no $k$-clique in $G$ or $G^c$. -/


namespace RamseyLocalLemma

open Finset Fintype RamseyLowerBound MeasureTheory ProbabilityTheory LovaszLocalLemma

end RamseyLocalLemma
