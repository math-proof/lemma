/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveMorphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Mathlib.Algebra.MvPolynomial.Monad
import Structure.v1.Atlas.ArithmeticGeometry.code.ProjectiveMorphisms.Part2


noncomputable section

open MvPolynomial

open scoped LinearAlgebra.Projectivization

namespace ProjectiveRegularFunction

variable {n : ℕ} (k : Type*) [Field k]

/-- The denominator of any representative of a projective rational function does not vanish identically on $X$ (else the function would be undefined everywhere). -/
def ProjectiveRatFun.IsRegularAt
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (_hP : P ∈ X) : Prop :=
  ∃ rep ∈ r.reps, rep.isDefinedAt k P

/-- The regular domain (locus of regularity) of a projective rational function: all points of $X$ where some representative is defined. -/
def ProjectiveRatFun.regularDomain
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X) :
    Set (ℙ k (Fin (n + 1) → k)) :=
  {P ∈ X | ∃ rep ∈ r.reps, rep.isDefinedAt k P}

/-- Evaluate a projective rational function $r$ at a point $P$ in its regular domain by choosing any representative defined at $P$ and evaluating it. -/
noncomputable def ProjectiveRatFun.evalAt
    {X : Set (ℙ k (Fin (n + 1) → k))}
    (r : ProjectiveRatFun n k X)
    (P : ℙ k (Fin (n + 1) → k))
    (hP : P ∈ r.regularDomain k) : k :=
  hP.2.choose.evalAt k P

end ProjectiveRegularFunction
end
