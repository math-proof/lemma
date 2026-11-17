/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/EilenbergZilber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Def.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
open CategoryTheory MonoidalCategory AlgebraicTopology

public section

noncomputable section

namespace EilenbergZilber

universe u

/-- **Theorem 25.13 (Eilenberg–Zilber theorem)**. There is a natural chain homotopy
equivalence
$$S_*(X; M) \otimes S_*(Y; M) \simeq S_*(X \times Y; M)$$
covering the canonical isomorphism in degree $0$. This packaged form provides both the
forward (shuffle) map and a chain homotopy inverse (Alexander–Whitney), unique up to
chain homotopy. -/
theorem. -/

end EilenbergZilber
end
