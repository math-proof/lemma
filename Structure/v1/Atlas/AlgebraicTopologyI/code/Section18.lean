/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.Torsion
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Section18
open Topology BigOperators AlgebraicTopology CategoryTheory


namespace EulerCharacteristic

/-- **Theorem 18.4** (Wall's theorem). Let $X$ be a simply connected CW-complex
of finite type. Then there exists a CW-complex $Y$ with exactly
$r(k) + t(k) + t(k - 1)$ cells in dimension $k$, together with a homotopy
equivalence $Y \to X$. -/
structure IsMooreSpace (M : Type) (tM : TopologicalSpace M)
    (cwM : @Topology.CWComplex M tM Set.univ) (A : AddCommGrpCat) (k : ℕ) : Prop where
  pathConnected : @PathConnectedSpace M tM
  homology_iso : Nonempty (((singularHomologyFunctor AddCommGrpCat k).obj
    (AddCommGrpCat.of ℤ)).obj (@TopCat.of M tM) ≅ A)
  homology_vanish : ∀ q, 0 < q → q ≠ k →
    @Limits.IsZero AddCommGrpCat _ (((singularHomologyFunctor AddCommGrpCat q).obj
      (AddCommGrpCat.of ℤ)).obj (@TopCat.of M tM))


end EulerCharacteristic
