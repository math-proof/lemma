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
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
public import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
open Topology BigOperators AlgebraicTopology CategoryTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section18.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace EulerCharacteristic

/-- The rank of an abelian group $A$, defined as
$\dim_{\mathbb{Q}} (A \otimes_{\mathbb{Z}} \mathbb{Q})$.

For a finitely generated abelian group $A \cong \mathbb{Z}^r \oplus T$ (with
$T$ torsion), this returns $r$, the number of $\mathbb{Z}$-summands. -/
noncomputable def abelianGroupRank (A : Type*) [AddCommGroup A] : ℕ :=
  Module.finrank ℚ (TensorProduct ℤ ℚ A)

/-- The number $a_n$ of $n$-cells in a CW-structure on $X$, i.e. the cardinality
of the indexing set of $n$-dimensional cells. -/
noncomputable def numCells (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : ℕ :=
  Nat.card (Topology.CWComplex.cell (Set.univ : Set X) n)

/-- The **Euler characteristic** of a CW-complex $X$ of dimension $< N$,
defined as the alternating sum
$$\chi(X) = \sum_{k=0}^{N-1} (-1)^k a_k$$
where $a_k$ is the number of $k$-cells. -/
noncomputable def eulerCharacteristic (X : Type*) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range N, (-1 : ℤ) ^ k * (numCells X k : ℤ)

/-- The $n$th Betti number of $X$: the $\mathbb{Z}$-rank of the singular
homology group $H_n(X; \mathbb{Z})$. -/
noncomputable def singularHomologyRank (X : Type) [TopologicalSpace X] (n : ℕ) : ℕ :=
  abelianGroupRank
    (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

/-- The differential $d_{k+1} : C_{k+1} \to C_k$ of a chain complex of abelian
groups, packaged as a $\mathbb{Z}$-linear map. -/
noncomputable def chainDifferentialLinearMap
    (C : ChainComplex AddCommGrpCat ℕ) (k : ℕ) : (C.X (k + 1)) →ₗ[ℤ] (C.X k) :=
  AddMonoidHom.toIntLinearMap (C.d (k + 1) k).hom

/-- The number of torsion coefficients of an abelian group $A$: the minimum
number of generators needed for its torsion subgroup. For a finitely generated
abelian group $A \cong \mathbb{Z}^r \oplus \bigoplus_i \mathbb{Z}/d_i$ this is
the number of cyclic torsion summands. -/
noncomputable def numTorsionCoeffs (A : Type*) [AddCommGroup A] : ℕ :=
  sInf {n : ℕ | ∃ (S : Finset (AddCommGroup.torsion A)),
    S.card = n ∧ AddSubgroup.closure (Subtype.val '' (S : Set (AddCommGroup.torsion A))) =
      AddCommGroup.torsion A}

/-- The minimal number of $k$-cells predicted by Wall's theorem:
$r(k) + t(k) + t(k - 1)$, where $r(k) = \operatorname{rank} H_k(X)$ is the
$k$th Betti number and $t(k)$ is the number of torsion coefficients of
$H_k(X)$. (For $k = 0$ the term $t(k - 1)$ is omitted.) -/
noncomputable def minimalCellCount (X : Type) [TopologicalSpace X] (k : ℕ) : ℕ :=
  let Hk : AddCommGrpCat :=
    ((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)
  EulerCharacteristic.abelianGroupRank Hk +
  numTorsionCoeffs Hk +
  (if k = 0 then 0
   else
    let Hk₁ : AddCommGrpCat :=
      ((singularHomologyFunctor AddCommGrpCat (k - 1)).obj
        (AddCommGrpCat.of ℤ)).obj (TopCat.of X)
    numTorsionCoeffs Hk₁)

end EulerCharacteristic
