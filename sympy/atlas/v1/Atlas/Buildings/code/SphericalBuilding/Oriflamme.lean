/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop_Bot.All_Eq

namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- A subspace $W \le V$ is **totally isotropic** for $B$ if $B(v, w) = 0$ for all
$v, w \in W$. -/
def IsTotallyIsotropic (W : Submodule k V) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, B v w = 0

/-- A totally isotropic subspace $W$ is **maximal** if it is not properly contained in any
larger totally isotropic subspace. -/
def IsMaximalTotallyIsotropic (W : Submodule k V) : Prop :=
  IsTotallyIsotropic k V B W ∧
  ∀ W' : Submodule k V, IsTotallyIsotropic k V B W' → W ≤ W' → W = W'

/-- The two $\mathrm{SO}(n, n)$-orbits of maximal isotropic $n$-subspaces, indexed by `Bool`
($V_1$ and $V_2$ in the oriflamme construction). -/
abbrev MaxIsotropicClass := Bool


/-- An **oriflamme vertex**: a nonzero totally isotropic subspace whose dimension is **not**
$n - 1$ (this dimension is excluded by the oriflamme construction). -/
def IsOriflammeVertex (W : Submodule k V) : Prop :=
  IsTotallyIsotropic k V B W ∧ W ≠ ⊥ ∧ Module.finrank k W ≠ n - 1

/-- **Oriflamme incidence**: two oriflamme vertices $x, y$ are incident if $x \subsetneq y$,
$y \subsetneq x$, or both are $n$-dimensional with $\dim(x \cap y) = n - 1$. -/
def OriflammeIncident (x y : Submodule k V) : Prop :=
  x < y ∨ y < x ∨
  (Module.finrank k x = n ∧ Module.finrank k y = n ∧
   Module.finrank k ↥(x ⊓ y) = n - 1)

/-- The **oriflamme complex** on $(V, B)$: a flag complex of oriflamme vertices, pairwise
incident, closed under nonempty subsets. -/
structure OriflammeComplex where
  simplices : Set (Finset (Submodule k V))
  simplex_vertices : ∀ σ ∈ simplices, ∀ W ∈ σ, IsOriflammeVertex k V B n W
  simplex_incident : ∀ σ ∈ simplices, ∀ W₁ ∈ σ, ∀ W₂ ∈ σ,
    OriflammeIncident k V n W₁ W₂
  face_closed : ∀ σ ∈ simplices, ∀ τ : Finset (Submodule k V),
    τ ⊆ σ → τ.Nonempty → τ ∈ simplices


/-- An **oriflamme chamber**: a maximal simplex in the oriflamme complex, consisting of an
isotropic chain $W_1 \subsetneq \cdots \subsetneq W_{n-2}$ of dimensions $1, \dots, n-2$
together with two distinct maximal isotropic $n$-subspaces $V_1 \ne V_2$ both containing
$W_{n-2}$ and meeting in dimension $n - 1$. -/
structure OriflammeChamber where
  chain : Fin (n - 2) → Submodule k V
  top₁ : Submodule k V
  top₂ : Submodule k V
  chain_strictMono : StrictMono chain
  chain_isotropic : ∀ i, IsTotallyIsotropic k V B (chain i)
  chain_dim : ∀ i : Fin (n - 2), Module.finrank k (chain i) = i.val + 1
  top₁_isotropic : IsTotallyIsotropic k V B top₁
  top₂_isotropic : IsTotallyIsotropic k V B top₂
  top₁_dim : Module.finrank k top₁ = n
  top₂_dim : Module.finrank k top₂ = n
  top₁_ne_top₂ : top₁ ≠ top₂
  chain_sub_tops : ∀ (h : 0 < n - 2), chain ⟨n - 3, by omega⟩ ≤ top₁ ⊓ top₂
  inter_dim : Module.finrank k ↥(top₁ ⊓ top₂) = n - 1


/-- An **oriflamme frame** of $(V, B)$: a hyperbolic frame as a decomposition into $n$
hyperbolic planes (one per index $i \in \mathrm{Fin}\, n$), each plane spanned by two isotropic
lines indexed by `Bool`. -/
structure OriflammeFrame where
  lines : Fin n × Bool → Submodule k V
  lines_isotropic : ∀ ib, IsTotallyIsotropic k V B (lines ib)
  lines_dim_one : ∀ ib, Module.finrank k (lines ib) = 1
  planes : Fin n → Submodule k V
  planes_eq : ∀ i, planes i = lines (i, true) ⊔ lines (i, false)
  span_top : ⨆ i, planes i = ⊤

/-- The **apartment** of the oriflamme complex $X$ associated to a frame $F$: the simplices
all of whose vertices are sums of frame lines. -/
def OriflammeApartment (X : OriflammeComplex k V B n) (F : OriflammeFrame k V B n) :
    Set (Finset (Submodule k V)) :=
  { σ ∈ X.simplices |
    ∀ W ∈ σ, ∃ S : Finset (Fin n × Bool),
      W = ⨆ ib ∈ S, F.lines ib }


/-- Witness that the oriflamme complex $X$ is a building of type $D_n$: a family of apartments
satisfying the common-apartment and apartment-exchange axioms. -/
structure OriflammeIsBuilding (X : OriflammeComplex k V B n) where
  apartments : Set (OriflammeFrame k V B n)
  common_apartment : ∀ σ₁ ∈ X.simplices, ∀ σ₂ ∈ X.simplices,
    ∃ F ∈ apartments, σ₁ ∈ OriflammeApartment k V B n X F ∧
      σ₂ ∈ OriflammeApartment k V B n X F
  apartment_exchange : ∀ F₁ ∈ apartments, ∀ F₂ ∈ apartments,
    (∃ C ∈ OriflammeApartment k V B n X F₁,
      C ∈ OriflammeApartment k V B n X F₂) →
    ∃ f : Submodule k V → Submodule k V,
      (∀ σ ∈ OriflammeApartment k V B n X F₁,
        σ.image f ∈ OriflammeApartment k V B n X F₂) ∧
      (∀ W, (∃ σ ∈ OriflammeApartment k V B n X F₁ ∩
        OriflammeApartment k V B n X F₂, W ∈ σ) →
        f W = W)

/-- The **isometry group** $O(V, B)$ of the bilinear form: all $k$-linear automorphisms of $V$
preserving $B$. -/
def OriflammeIsometryGroup : Set (V ≃ₗ[k] V) :=
  { g | ∀ v₁ v₂, B (g v₁) (g v₂) = B v₁ v₂ }

/-- The oriflamme building is **strongly transitive** under $\mathrm{SO}(V, B)$ if any pair
of frame/chamber data in two apartments can be mapped one to the other by an isometry. -/
def SO_StronglyTransitive (X : OriflammeComplex k V B n)
    (bldg : OriflammeIsBuilding k V B n X) : Prop :=
  ∀ (F₁ F₂ : OriflammeFrame k V B n),
    F₁ ∈ bldg.apartments → F₂ ∈ bldg.apartments →
    ∀ C₁ ∈ OriflammeApartment k V B n X F₁,
    ∀ C₂ ∈ OriflammeApartment k V B n X F₂,
    ∃ g ∈ OriflammeIsometryGroup k V B,
      (∀ ib, (F₁.lines ib).map g.toLinearMap = F₂.lines ib) ∧
      (∀ W ∈ C₁, ∃ W' ∈ C₂, W.map g.toLinearMap = W')


/-- **B-N pair data** for the oriflamme building: Borel and frame-stabiliser subsets of the
isometry group, an oriflamme chamber, a frame, and the Bruhat decomposition
$G = B \cdot W \cdot B$. -/
structure BNPairData where
  borelSet : Set (V ≃ₗ[k] V)
  frameStabSet : Set (V ≃ₗ[k] V)
  borel_sub : borelSet ⊆ OriflammeIsometryGroup k V B
  frameStab_sub : frameStabSet ⊆ OriflammeIsometryGroup k V B
  chamber : OriflammeChamber k V B n
  borel_stab_chain : ∀ g ∈ borelSet, ∀ i,
    (chamber.chain i).map g.toLinearMap = chamber.chain i
  borel_stab_top₁ : ∀ g ∈ borelSet,
    chamber.top₁.map g.toLinearMap = chamber.top₁
  borel_stab_top₂ : ∀ g ∈ borelSet,
    chamber.top₂.map g.toLinearMap = chamber.top₂
  frame : OriflammeFrame k V B n
  frameStab_permutes : ∀ g ∈ frameStabSet, ∀ ib : Fin n × Bool,
    ∃ jb : Fin n × Bool, (frame.lines ib).map g.toLinearMap = frame.lines jb
  bruhat : ∀ g ∈ OriflammeIsometryGroup k V B,
    ∃ w ∈ frameStabSet, ∃ b₁ ∈ borelSet, ∃ b₂ ∈ borelSet,
      g = b₁.trans (w.trans b₂)


/-- A Coxeter matrix is of **type $D_n$** ($n \ge 3$): linear $A_{n-2}$ chain
$1 - 2 - \cdots - (n-2)$ with two extra nodes branching off node $n-3$ at angle $3$ and
commuting with each other ($m = 2$). -/
def TypeDn (hn : n ≥ 3) : Prop :=
  ∃ (m : Fin n → Fin n → ℕ),

    (∀ i, m i i = 1) ∧

    (∀ i j, m i j = m j i) ∧

    (∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      m i j = 3) ∧

    (m ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ = 3) ∧
    (m ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ = 3) ∧

    (m ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 2) ∧

    (∀ i j : Fin n, i ≠ j → m i j ≠ 1 →
      m i j = 2 ∨ m i j = 3)

/-- The maximal isotropic $n$-subspace $W$ belongs to **orbit class** $\mathrm{cls}$ relative
to the frame $F$ if $W$ is a sum of $n$ frame lines whose parity of `false`-indexed lines
matches $\mathrm{cls}$ (even for `true`, odd for `false`). -/
def IsInOrbitClass (F : OriflammeFrame k V B n) (W : Submodule k V)
    (cls : MaxIsotropicClass) : Prop :=
  IsTotallyIsotropic k V B W ∧
  Module.finrank k W = n ∧
  ∃ (S : Finset (Fin n × Bool)),
    S.card = n ∧
    W = ⨆ ib ∈ S, F.lines ib ∧

    (S.filter (fun ib => ib.2 = false)).card % 2 = if cls then 0 else 1


section DetIsometry

variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
         [FiniteDimensional k' V']

/-- The **special isometry group** $\mathrm{SO}(V, B) = \{g : g \text{ isometry}, \det g = 1\}$. -/
def SpecialIsometryGroup (B' : LinearMap.BilinForm k' V') : Set (V' ≃ₗ[k'] V') :=
  { g | (∀ v w, B' (g v) (g w) = B' v w) ∧ (g : V' →ₗ[k'] V').det = 1 }

end DetIsometry


section HypSwap

variable {k' : Type*} [Field k']
