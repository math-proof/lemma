/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.Language
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Lattice
import Inductive.v1.Atlas.TheoryOfComputation.code.ContextFree.Part3


namespace ChomskyNormalForm

variable {T : Type*}

namespace CNFParseTree

/-- The *yield* of a parse tree: the list of terminals at its leaves, read
left-to-right. -/
def yield : CNFParseTree g A → List T
  | .leaf _ a _ => [a]
  | .node _ _ _ _ l r => l.yield ++ r.yield

/-- The *height* of a parse tree: leaves have height `0`, and an internal node
has height `1 + max(height(left), height(right))`. -/
def height : CNFParseTree g A → ℕ
  | .leaf _ _ _ => 0
  | .node _ _ _ _ l r => max l.height r.height + 1

/-- The nonterminal label appearing at depth `d` along the *tallest path* of `t`
(breaking ties by descending into the left subtree). The pumping argument inspects
this sequence of labels to find a repeat by pigeonhole. -/
def ntAtDepth : {A : g.NT} → (t : CNFParseTree g A) → (d : ℕ) → (hd : d ≤ t.height) → g.NT
  | A, _, 0, _ => A
  | _, .node _ _ _ _ l r, d + 1, hd =>
    if h : l.height ≥ r.height then
      ntAtDepth l d (by simp [height] at hd; omega)
    else
      ntAtDepth r d (by simp [height] at hd; omega)

end CNFParseTree
end ChomskyNormalForm
