/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LatinSquares.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
set_option maxHeartbeats 400000

open Function


namespace LatinSquares

/-- An $n \times n$ array $L : \text{Fin}\ n \to \text{Fin}\ n \to \text{Fin}\ n$ is a Latin square if every row and every column is a permutation of $\{0,1,\dots,n-1\}$, equivalently if every row map and every column map is injective. -/
structure IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop where
  row_injective : ∀ i : Fin n, Injective (L i)
  col_injective : ∀ j : Fin n, Injective (fun i => L i j)

end LatinSquares
