/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter4/CliqueNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
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
