/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Torsors
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.EllipticCurves
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EllipticCurves
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Divisors

noncomputable section

universe u

/-- Abstract predicate: the type `C_pts` represents the points of a smooth curve of arithmetic
genus 1 over $k$. The concrete content is deferred via `sorry`. -/
variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}


/-- An $E$-torsor over $k$ is nonempty (since `AddTorsor` requires nonemptiness). -/
namespace ETorsor

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts]

/-- Two $E$-torsors $T_1, T_2$ are *equivalent* if there is a $k$-isomorphism $C_{T_1} \simeq C_{T_2}$
that intertwines the $E$-actions: $e(p +_v q) = p +_v e(q)$. -/
end ETorsor

/-- The *Weil-Châtelet set* of $E/k$: the set of $E$-torsors over $k$ up to $k$-isomorphism,
realised as the quotient of `ETorsor` by the equivalence relation. -/
namespace ETorsorPic

section PiConstruction

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]

/-- The scalar multiplication $n \mapsto n \cdot e$ packaged as an additive homomorphism
$\mathbb{Z} \to E$. -/
def zsmulHom (e : E_pts) : ℤ →+ E_pts where
  toFun n := n • e
  map_zero' := zero_smul ℤ e
  map_add' m n := add_smul m n e

/-- The Abel-Jacobi map at the level of free abelian groups: $\sum n_P [P] \mapsto
\sum n_P (P -_v Q_0)$, viewed as an additive homomorphism $(C \to_0 \mathbb{Z}) \to E$. -/
def piMap (Q₀ : C_pts) : (C_pts →₀ ℤ) →+ E_pts :=
  Finsupp.liftAddHom (fun P => zsmulHom (P -ᵥ Q₀ : E_pts))

/-- The degree homomorphism on the free abelian group on $C$: $\sum n_P [P] \mapsto \sum n_P$. -/
def piDegreeMap : (C_pts →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

/-- Evaluation of `piMap` on a single basis element: $\mathrm{piMap}\,Q_0\,[P]_n = n \cdot (P -_v Q_0)$. -/
@[simp] theorem piMap_single (Q₀ P : C_pts) (n : ℤ) :
    piMap Q₀ (Finsupp.single P n) = n • (P -ᵥ Q₀ : E_pts) := by
  simp [piMap, zsmulHom]

/-- The degree map sends a single basis element $[P]_n$ to $n$. -/
@[simp] theorem piDegreeMap_single (P : C_pts) (n : ℤ) :
    piDegreeMap (Finsupp.single P n) = n := by
  simp [piDegreeMap]

/-- The Abel-Jacobi map `piMap Q₀` is surjective: every element of $E$ can be realised as the
image of a divisor of degree zero. -/
theorem piMap_surjective (Q₀ : C_pts) : Function.Surjective (piMap Q₀) := by
  intro P
  use Finsupp.single (P +ᵥ Q₀) 1 - Finsupp.single Q₀ 1
  simp only [map_sub, piMap_single, one_smul, vadd_vsub, vsub_self, sub_zero]

/-- Auxiliary data for the Abel-Jacobi isomorphism $\mathrm{Pic}^0(C) \simeq E$: a factorisation
of the Abel-Jacobi map $\pi$ through an intermediate group `DivZero_E`, together with the
inclusion of principal divisors and a "function field" compatibility condition. -/
structure EllipticCurveDivisorData
    (E_pts : Type u) [AddCommGroup E_pts]
    (DivZero : Type u) [AddCommGroup DivZero]
    (DivZero_E : Type u) [AddCommGroup DivZero_E]
    (PrincDiv : AddSubgroup DivZero) (π : DivZero →+ E_pts) where
  PrincDiv_E : AddSubgroup DivZero_E
  τ : DivZero →+ DivZero_E
  σ_E : DivZero_E →+ E_pts
  hπ_factor : ∀ D, π D = σ_E (τ D)
  abel_on_E : σ_E.ker ≤ PrincDiv_E
  func_field : ∀ D, τ D ∈ PrincDiv_E → D ∈ PrincDiv

section Pic0IsoE

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]
  {DivZero : Type u} [AddCommGroup DivZero]
  (PrincDiv : AddSubgroup DivZero)
  (π : DivZero →+ E_pts)

/-- The kernel of the Abel-Jacobi map $\pi$ is contained in the principal divisors:
$\ker(\pi) \subseteq \mathrm{Princ}$. -/
theorem abel_jacobi_ker_le_princDiv
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π) :
    π.ker ≤ PrincDiv := by
  intro D hD
  rw [AddMonoidHom.mem_ker] at hD

  have h1 : data.σ_E (data.τ D) = 0 := by rw [← data.hπ_factor]; exact hD
  have h2 : data.τ D ∈ data.σ_E.ker := by rwa [AddMonoidHom.mem_ker]

  have h3 : data.τ D ∈ data.PrincDiv_E := data.abel_on_E h2

  exact data.func_field D h3

/-- Conversely, principal divisors are contained in the kernel of $\pi$, provided the converse
versions of the `EllipticCurveDivisorData` axioms hold. -/
theorem princDiv_le_ker_pi
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    PrincDiv ≤ π.ker := by
  intro D hD
  rw [AddMonoidHom.mem_ker]

  have h1 : data.τ D ∈ data.PrincDiv_E := hfunc_field_converse D hD

  have h2 : data.τ D ∈ data.σ_E.ker := habel_converse h1
  rw [AddMonoidHom.mem_ker] at h2

  rw [data.hπ_factor D, h2]

/-- Combining the two inclusions: $\ker(\pi) = \mathrm{Princ}$. -/
theorem piMap_ker_eq_princDiv
    (hπ_ker_le : π.ker ≤ PrincDiv) (hπ_principal_in_ker : PrincDiv ≤ π.ker) :
    π.ker = PrincDiv :=
  le_antisymm hπ_ker_le hπ_principal_in_ker

/-- The Abel-Jacobi isomorphism: assuming the abstract divisor data and surjectivity of $\pi$,
one has $\mathrm{Pic}^0(C) = \mathrm{Div}^0/\mathrm{Princ} \cong E$. -/
noncomputable def pic0_addEquiv_E
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) : DivZero ⧸ PrincDiv ≃+ E_pts :=
  have hπ_ker_le : π.ker ≤ PrincDiv := abel_jacobi_ker_le_princDiv PrincDiv π data
  have hπ_principal_in_ker : PrincDiv ≤ π.ker :=
    princDiv_le_ker_pi PrincDiv π data habel_converse hfunc_field_converse
  (piMap_ker_eq_princDiv PrincDiv π hπ_ker_le hπ_principal_in_ker) ▸
    QuotientAddGroup.quotientKerEquivOfSurjective π hπ_surj

/-- Theorem 26.17 (concrete form): the Abel-Jacobi isomorphism
$\mathrm{Pic}^0(C) \cong E$ obtained from the concrete `piMap` and a divisor data. -/
noncomputable def theorem_26_17_pic0_iso
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀))
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    (C_pts →₀ ℤ) ⧸ PrincDiv ≃+ E_pts :=
  pic0_addEquiv_E PrincDiv (piMap Q₀) data habel_converse hfunc_field_converse
    (piMap_surjective Q₀)
