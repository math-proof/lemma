/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Structure.v1.Atlas.Buildings.code.Building.AffineSLV.Part2
set_option linter.unusedSectionVars false


namespace AffineBuildingSLV

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- The vertices of a maximal simplex extracted from a periodic flag: take the
homothety classes of $\Lambda_0, \ldots, \Lambda_{n-1}$. -/
def PeriodicFlag.toVertices (pf : PeriodicFlag C) :
    Fin C.n → DVRContext.HomothetyClass C :=
  fun j => Quot.mk _ (pf.lattice (j : ℤ))

/-- A simplex is maximal (a chamber) if it has exactly $n$ vertices and cannot be
extended: any further vertex fails to be incident to at least one vertex of
$\sigma$. -/
def Simplex.IsMaximal (σ : Simplex C) : Prop :=
  σ.vertices.card = C.n ∧
  ∀ ξ : DVRContext.HomothetyClass C,
    ξ ∉ σ.vertices →
    ∃ η ∈ σ.vertices, ¬ IncidenceRel C ξ η

end AffineBuildingSLV


namespace AffineBuildingSLVAxioms

set_option linter.unusedVariables false

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- The Coxeter matrix of the affine type $\tilde A_{n-1}$ on $\mathbb{Z}/n$
generators: label $1$ on the diagonal, $3$ on edges of the cyclic Dynkin
diagram, and $2$ elsewhere. -/
def CoxeterMatrixAffineA (n : ℕ) (i j : ZMod n) : ℕ :=
  if i = j then 1
  else if i = j + 1 ∨ j = i + 1 then 3
  else 2

/-- A lattice $\Lambda'$ is a valid replacement for the $i$-th lattice of a
periodic flag $\mathit{pf}$ if it lies between
$\mathit{pf}_{i-1}$ and $\mathit{pf}_{i+1}$. -/
def IsValidReplacement (pf : AffineBuildingSLV.PeriodicFlag C)
    (i : Fin C.n) (Λ' : DVRContext.OLattice C) : Prop :=
  (pf.lattice ((i : ℤ) - 1)).carrier ⊆ Λ'.carrier ∧
  Λ'.carrier ⊆ (pf.lattice ((i : ℤ) + 1)).carrier

/-- The transposition $(i\ i+1)$ swapping the $i$-th and $(i+1)$-th vertices,
representing reflection in the facet opposite vertex $i$ of a chamber. -/
def FacetReflection (n : ℕ) (i : Fin n) : Fin n → Fin n :=
  fun j => if j = i then (if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else j)
           else if h : j.val = i.val + 1 then ⟨i.val, i.isLt⟩
           else j

/-- The vertex label of $\Lambda$ relative to a base lattice: a class in
$\mathbb{Z}/n$ encoding the "level" of $\Lambda$ in the lattice chain. -/
def VertexLabel (_base Λ : DVRContext.OLattice C) (inv_factor_sum : ℕ) : ZMod C.n :=
  (inv_factor_sum : ZMod C.n)


/-- A matrix over $\mathfrak{o}$ is upper-triangular modulo $\mathfrak{m}$ if
every strictly below-diagonal entry is a multiple of the uniformizer $\pi$. -/
def IsUpperTriangularModM (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, i.val > j.val →
    ∃ h : C.𝔬, g i j = C.uniformizer * h

/-- A matrix over $\mathfrak{o}$ is congruent to the identity modulo
$\mathfrak{m}$ if each entry equals the corresponding entry of the
identity matrix modulo $\pi$. -/
def IsCongruentToIdentityModM (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, ∃ h : C.𝔬,
    g i j - (if i = j then 1 else 0) = C.uniformizer * h

/-- A matrix $g$ stabilises the standard periodic flag $(\Lambda_i)_i$ if its
linear action preserves each $\Lambda_i$ setwise. -/
def StabilizesStandardFlag
    (g : Fin C.n → Fin C.n → C.𝔬)
    (pf : AffineBuildingSLV.PeriodicFlag C) : Prop :=
  ∀ i : Fin C.n, ∀ v ∈ (pf.lattice (i : ℤ)).carrier,
    (fun j => ∑ l, C.embed (g j l) * v l) ∈ (pf.lattice (i : ℤ)).carrier

end AffineBuildingSLVAxioms
