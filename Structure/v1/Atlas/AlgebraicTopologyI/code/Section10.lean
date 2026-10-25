/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10.Part11
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

/-- **Proposition 10.4 (packaged).** The singular homology of spheres and the relative
homology of disk pairs: `H_n(S^n) = ℤ`, `H_0(S^n) = ℤ` for `n > 0`,
`H_0(S^0) = ℤ ⊕ ℤ`, otherwise zero; and `H_n(D^n, S^{n-1}) = ℤ`, otherwise zero. -/
structure SphereAndDiskHomology : Prop where
  sphere_top : ∀ (n : ℕ), n > 0 →
    Nonempty (SingularHomologyGroup n (Sphere n) ≅ AddCommGrpCat.of ℤ)
  sphere_zero : ∀ (n : ℕ), n > 0 →
    Nonempty (SingularHomologyGroup 0 (Sphere n) ≅ AddCommGrpCat.of ℤ)
  sphere_zero_zero :
    Nonempty (SingularHomologyGroup 0 (Sphere 0) ≅ AddCommGrpCat.of (ℤ × ℤ))
  sphere_vanishing : ∀ (q n : ℕ), n > 0 → q ≠ 0 → q ≠ n →
    IsZero (SingularHomologyGroup q (Sphere n))
  sphere_zero_vanishing : ∀ (q : ℕ), q > 0 →
    IsZero (SingularHomologyGroup q (Sphere 0))
  relative_top : ∀ (n : ℕ), n > 0 →
    Nonempty (Excision.RelativeSingularHomologyGroup n (Disk n) (diskBoundarySubset n) ≅
      AddCommGrpCat.of ℤ)
  relative_vanishing : ∀ (q n : ℕ), n > 0 → q ≠ n →
    IsZero (Excision.RelativeSingularHomologyGroup q (Disk n) (diskBoundarySubset n))


end SphereHomology
