/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Topology.Algebra.Ring.Real

@[expose] public section

set_option maxHeartbeats 400000

open scoped Classical
open Finset BigOperators Filter Topology


namespace CliqueNumber

/-- Expected number of $k$-cliques in the random graph $G(n, 1/2)$,
    equal to $\binom{n}{k} \cdot 2^{-\binom{k}{2}}$. -/
noncomputable def expectedKCliques (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (2 : ℝ) ^ (-(k.choose 2 : ℤ))

/-- Probability under the uniform measure on simple graphs on $\{1,\dots,n\}$
    (equivalently $G(n, 1/2)$) that the graph contains a clique of size at least $k$. -/
noncomputable def probCliqueGe (n k : ℕ) : ℝ :=
  ((Finset.univ.filter (fun G : SimpleGraph (Fin n) => ¬G.CliqueFree k)).card : ℝ) /
  (Fintype.card (SimpleGraph (Fin n)) : ℝ)

end CliqueNumber
