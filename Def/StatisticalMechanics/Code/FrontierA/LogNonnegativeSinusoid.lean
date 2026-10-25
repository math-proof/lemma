/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LogNonnegativeSinusoid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Polynomial.MahlerMeasure
open scoped ComplexConjugate
open MeasureTheory Polynomial


namespace StatMech.FrontierA

noncomputable def nonnegativeSinusoidQ (A u v : Real) : Real :=
  A + Real.sqrt (A ^ 2 - (u ^ 2 + v ^ 2))

noncomputable def nonnegativeSinusoidRoot (A u v : Real) : Complex :=
  (u + v * Complex.I) / nonnegativeSinusoidQ A u v

noncomputable def nonnegativeSinusoidPolynomial (A u v : Real) : Polynomial Complex :=
  let q := nonnegativeSinusoidQ A u v
  let a := nonnegativeSinusoidRoot A u v
  C ((q / 2 : Real) : Complex) *
    (X - C a) * (1 - C (conj a) * X)

end StatMech.FrontierA
