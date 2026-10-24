/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerEntropy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.Entropy
import Mathlib.Data.Finset.Card

open Finset BigOperators ShannonEntropy Real

namespace ShearerEntropy

/-- The marginal distribution of a joint PMF $p$ on `Fin n → Ω` restricted to coordinates in
$A \subseteq \{1,\dots,n\}$. -/
noncomputable def marginal {n : ℕ} {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : PMF (Fin n → Ω)) (A : Finset (Fin n)) : PMF (↥A → Ω) :=
  p.map (fun x (i : ↥A) => x i.val)

/-- The covering condition for Shearer's lemma: a family $\{A_j\}_{j=1}^s$ is a $k$-cover of
$\{1,\dots,n\}$ if every index appears in at least $k$ of the sets $A_j$. -/
def CoveringCondition {n s : ℕ} (A : Fin s → Finset (Fin n)) (k : ℕ) : Prop :=
  ∀ i : Fin n, k ≤ (Finset.univ.filter (fun j => i ∈ A j)).card
