/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Torsors
import Def.v1.Atlas.ArithmeticGeometry.code.EllipticCurves.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EllipticCurves
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Divisors
import Def.v1.Atlas.ArithmeticGeometry.code.Divisors.Part11
import Structure.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
/-- Abstract predicate: the type `C_pts` represents the points of a smooth curve of arithmetic
genus 1 over $k$. The concrete content is deferred via `sorry`. -/
/-- An $E$-torsor over $k$ is nonempty (since `AddTorsor` requires nonemptiness). -/
/-- Two $E$-torsors $T_1, T_2$ are *equivalent* if there is a $k$-isomorphism $C_{T_1} \simeq C_{T_2}$
that intertwines the $E$-actions: $e(p +_v q) = p +_v e(q)$. -/
/-- The *Weil-Châtelet set* of $E/k$: the set of $E$-torsors over $k$ up to $k$-isomorphism,
realised as the quotient of `ETorsor` by the equivalence relation. -/


namespace ETorsor

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts]

end ETorsor

noncomputable section

universe u

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}


namespace ETorsorPic

section PiConstruction

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]

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

end Pic0IsoE
end PiConstruction
end ETorsorPic
end
