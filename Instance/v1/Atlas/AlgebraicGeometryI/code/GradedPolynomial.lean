/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GradedPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Polynomial.HilbertPoly
set_option maxHeartbeats 800000

open MvPolynomial


noncomputable section

/-- Finiteness instance: monomials in `n` variables of total degree `d` form a finite set. -/
instance Finsupp.fintypeDegreeEq (n d : ℕ) :
    Fintype {s : Fin n →₀ ℕ | s.degree = d} :=
  ((Finsupp.finite_of_degree_le d).subset (fun _ hx => le_of_eq hx)).fintype

end
