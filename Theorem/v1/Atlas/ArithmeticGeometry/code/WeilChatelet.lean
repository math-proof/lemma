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
import Def.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
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

end PiConstruction
end ETorsorPic
end
