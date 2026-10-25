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
import Theorem.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
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

end PiConstruction
end ETorsorPic
end
