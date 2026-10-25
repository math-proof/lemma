/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/ListChromatic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable.Part2
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter1.TwoColorable
set_option maxHeartbeats 800000


namespace ListChromatic

open Finset

/-- `IsKChoosable n k` says that the complete bipartite graph $K_{n,n}$ is $k$-choosable
in the combinatorial sense: for any color set $C$ and any pair of list assignments
$L, R : [n] \to \binom{C}{\ge k}$, there exist representatives $cL_i \in L_i$ and
$cR_j \in R_j$ with $cL_i \ne cR_j$ for all $i, j$. -/
def IsKChoosable (n k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] (L R : Fin n → Finset C),
    (∀ i, k ≤ (L i).card) →
    (∀ j, k ≤ (R j).card) →
    ∃ (cL : Fin n → C) (cR : Fin n → C),
      (∀ i, cL i ∈ L i) ∧
      (∀ j, cR j ∈ R j) ∧
      (∀ i j, cL i ≠ cR j)

end ListChromatic
