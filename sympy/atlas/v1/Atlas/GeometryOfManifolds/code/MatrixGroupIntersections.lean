/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MatrixGroupIntersections.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

namespace CompatibleTriple

variable (l : Type*) [DecidableEq l] [Fintype l]

/-- The symplectic group $\mathrm{Sp}(2n) = \{A : A^T J A = J\}$, realized as a set of
real $(l \sqcup l) \times (l \sqcup l)$ matrices using the standard symplectic form $J$. -/
def Sp2n : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  { A | A.transpose * J l ℝ * A = J l ℝ }

/-- The orthogonal group $O(2n) = \{A : A^T A = I\}$. -/
def O2n : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  { A | A.transpose * A = 1 }

/-- The subgroup of $\mathrm{GL}(2n, \mathbb{R})$ that commutes with $J$, identified with
$\mathrm{GL}(n, \mathbb{C}) = \{A : AJ = JA\}$ via the standard complex structure $J$. -/
def GLnC : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  { A | A * J l ℝ = J l ℝ * A }

/-- The unitary group $U(n) = \mathrm{GL}(n, \mathbb{C}) \cap O(2n)$. -/
def Un : Set (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
  GLnC l ∩ O2n l

variable {l}
