/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvarianceTopCat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Module.PID
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
public import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section18
public section

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
