/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/JohnsonLindenstrauss.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

set_option maxHeartbeats 800000

noncomputable section

open Real Finset

/-- **Probabilistic core of the Johnson–Lindenstrauss lemma.** There exists $c > 0$ such that
whenever the union-bound quantity $N^{2}\,(2\,e^{-c\varepsilon^{2}d})$ is strictly less than
$1$, any $N$-point subset $X \subseteq \mathbb{R}^m$ admits a map $f : \mathbb{R}^m \to
\mathbb{R}^d$ that preserves all pairwise distances up to a factor of $1 \pm \varepsilon$. -/
namespace JohnsonLindenstrauss

/-- **Johnson–Lindenstrauss lemma** (Theorem 9.4.22, Johnson–Lindenstrauss 1982). There exists a
constant $C > 0$ such that for every $\varepsilon > 0$, every finite set
$X \subseteq \mathbb{R}^m$ of size $N \ge 2$, and every target dimension
$d > C\varepsilon^{-2}\log N$, there is a map $f : \mathbb{R}^m \to \mathbb{R}^d$ preserving
all pairwise distances within a factor of $1 \pm \varepsilon$. -/
end JohnsonLindenstrauss

end
