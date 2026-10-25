/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/NewtonPolygon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Set.Card
import Def.v1.Atlas.EllipticCurves.code.NewtonPolygon


noncomputable section

open scoped Classical

/-- A bundle of data witnessing the existence of a "genus" function on bivariate
polynomials over `k`, packaging invariance under nonzero scaling, the arithmetic
genus upper bound, and the equality case for smooth curves. -/
class FunctionField.GenusData (k : Type*) [Field k] where
  genusVal : MvPolynomial (Fin 2) k → ℕ
  genus_invariant_val : ∀ (f : MvPolynomial (Fin 2) k) (c : k), c ≠ 0 →
    genusVal (MvPolynomial.C c * f) = genusVal f
  genus_le_arithmetic_genus_val : ∀ (f : MvPolynomial (Fin 2) k),
    Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) →
    genusVal f ≤ (f.totalDegree - 1) * (f.totalDegree - 2) / 2
  genus_eq_arithmetic_genus_of_smooth_val : ∀ (f : MvPolynomial (Fin 2) k),
    Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) →
    (∀ p : Fin 3 → AlgebraicClosure k,
      (∃ i, p i ≠ 0) →
      ¬NewtonPolygon.IsSingularPoint
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) (NewtonPolygon.homogenize f)) p) →
    genusVal f = (f.totalDegree - 1) * (f.totalDegree - 2) / 2

end
