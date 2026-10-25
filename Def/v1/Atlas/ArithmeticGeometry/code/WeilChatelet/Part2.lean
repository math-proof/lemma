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
import Theorem.v1.Atlas.ArithmeticGeometry.code.WeilChatelet.Part2
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

end Pic0IsoE
end PiConstruction
end ETorsorPic
end
