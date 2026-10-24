/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/CellDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Set MvPolynomial

namespace CellDecomposition

/--
A line in `ℝ²`: a one-dimensional affine subspace, packaged with a proof that
its direction has rank `1` and that its carrier set is nonempty.
-/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

/-- Membership of a point in a `Line2`: belongs to the underlying affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier


/--
Polynomial ham-sandwich theorem for finite sets in `ℝ²`. Given at most `D²`
finite sets `S_i ⊆ ℝ²`, there is a nonzero polynomial `p` of total degree at
most `D` such that for each `i`, both `{x ∈ S_i : p(x) > 0}` and
`{x ∈ S_i : p(x) < 0}` contain at most half of `S_i`.
-/
noncomputable def polyCell {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) : Set (Fin 2 → ℝ) :=
  ⋂ i, if σ i then {x | eval x (polys i) > 0}
              else {x | eval x (polys i) < 0}

/--
The "wall" `⋃_i Z(polys i)`: the union of the zero sets of the polynomials,
separating the open cells `polyCell polys σ`.
-/
def polyWall {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) : Set (Fin 2 → ℝ) :=
  ⋃ i, {x | eval x (polys i) = 0}

/--
The points of a finite set `X ⊆ ℝ²` lying in the open cell `polyCell polys σ`,
returned as a `Finset`.
-/
noncomputable def signPatternCell (X : Finset (Fin 2 → ℝ))
    {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) (σ : Fin k → Bool) :
    Finset (Fin 2 → ℝ) :=
  X.filter (fun x => ∀ i, if σ i then eval x (polys i) > 0 else eval x (polys i) < 0)
