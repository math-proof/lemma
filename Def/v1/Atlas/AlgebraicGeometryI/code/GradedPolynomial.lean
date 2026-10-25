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
import Instance.v1.Atlas.AlgebraicGeometryI.code.GradedPolynomial
set_option maxHeartbeats 800000

open MvPolynomial


noncomputable section

/-- Equivalence between degree-`d` monomials in `n` variables and `d`-element multisets in `Fin n`. -/
def degreeEquivSym (n d : ℕ) :
    {s : Fin n →₀ ℕ | s.degree = d} ≃ Sym (Fin n) d :=
  (Equiv.subtypeEquivRight (fun s => by simp [Finsupp.degree, Finsupp.sum, id])).trans
    (Sym.equivNatSum (Fin n) d).symm

/-- The Hilbert function of `P^n_k`: dimension of degree-`d` forms in `n + 1` variables. -/
def hilbertFun (k : Type*) [Field k] (n : ℕ) (d : ℕ) : ℕ :=
  Module.finrank k (homogeneousSubmodule (Fin (n + 1)) k d)

/-- Hilbert function of a quotient ring: dimension of the degree-`d` part of
`k[x_0, ..., x_n] / I`. -/
def hilbertFunQuotient (k : Type*) [Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) (d : ℕ) : ℕ :=
  Module.finrank k (homogeneousSubmodule (Fin (n + 1)) k d ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) k d).subtype
      (I.restrictScalars k))

end
