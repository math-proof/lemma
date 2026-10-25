/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section1


namespace AlgebraicTopologyI

open Finset AlgebraicTopology CategoryTheory

/-- The integer-graded variant of singular chains: equals $S_n(X)$ for $n \ge 0$ and is
trivial for $n < 0$. Convenient for stating chain-complex axioms uniformly. -/
def SingularChainsZ (n : ℤ) (X : Type*) [TopologicalSpace X] : Type _ :=
  if n ≥ 0 then SingularChains n.toNat X else PUnit

/-- A chain $c \in A$ is a cycle with respect to a boundary map $d : A \to B$ if
$d(c) = 0$. -/
def IsCycle {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (d : A →+ B) (c : A) : Prop :=
  d c = 0

/-- The subgroup of cycles for a boundary map $d : A \to B$: the kernel of $d$. -/
def Cycles {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (d : A →+ B) : AddSubgroup A :=
  d.ker

/-- The singular $n$-cycles of $X$ with respect to a given boundary map $d$:
$Z_{n+1}(X) = \ker (d : S_{n+1}(X) \to S_n(X))$. -/
def SingularCycles (n : ℕ) (X : Type*) [TopologicalSpace X]
    (d : SingularChains (n + 1) X →+ SingularChains n X) :
    AddSubgroup (SingularChains (n + 1) X) :=
  Cycles d

end AlgebraicTopologyI
