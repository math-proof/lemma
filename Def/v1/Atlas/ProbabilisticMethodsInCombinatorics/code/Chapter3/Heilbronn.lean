/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/Heilbronn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
set_option maxHeartbeats 800000

open Set Finset


namespace Heilbronn

/-- The closed unit square $[0,1]^2 \subseteq \mathbb{R}^2$. -/
def unitSquare : Set (ℝ × ℝ) := Set.Icc (0, 0) (1, 1)

/-- The area of the triangle with vertices $p, q, r \in \mathbb{R}^2$, computed via the
absolute value of half the cross product of $(q-p)$ and $(r-p)$. -/
noncomputable def triangleArea (p q r : ℝ × ℝ) : ℝ :=
  |((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1))| / 2

/-- The minimum triangle area among all triples of distinct points in a finite set
$S \subseteq \mathbb{R}^2$. -/
noncomputable def minTriangleArea (S : Finset (ℝ × ℝ)) : ℝ :=
  sInf {a : ℝ | ∃ p ∈ S, ∃ q ∈ S, ∃ r ∈ S,
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ a = triangleArea p q r}

/-- The Heilbronn number $H(n)$: the supremum, over all $n$-point configurations in the
unit square, of the minimum triangle area among triples of points in the configuration. -/
noncomputable def heilbronnNumber (n : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ S : Finset (ℝ × ℝ), S.card = n ∧
    (↑S : Set (ℝ × ℝ)) ⊆ unitSquare ∧ a = minTriangleArea S}

/-- For prime $p$ and $i \in \{0, 1, \dots, p-1\}$, the point $(i/p, (i^2 \bmod p)/p)$
on the discretized parabola in the unit square. -/
noncomputable def parabolaPoint (p : ℕ) (i : Fin p) : ℝ × ℝ :=
  ((i.val : ℝ) / (p : ℝ), ((i.val ^ 2 % p : ℕ) : ℝ) / (p : ℝ))

/-- The integer cross-product determinant associated with three points on the parabola at
indices $a, b, c \in \mathbb{F}_p$. -/
def intDetFin {p : ℕ} (a b c : Fin p) : ℤ :=
  ((b.val : ℤ) - a.val) * (((c.val ^ 2 % p : ℕ) : ℤ) - ((a.val ^ 2 % p : ℕ) : ℤ)) -
  (((b.val ^ 2 % p : ℕ) : ℤ) - ((a.val ^ 2 % p : ℕ) : ℤ)) * ((c.val : ℤ) - a.val)

end Heilbronn
