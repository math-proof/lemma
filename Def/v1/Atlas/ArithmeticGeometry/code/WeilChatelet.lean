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

end PiConstruction
end ETorsorPic
end
