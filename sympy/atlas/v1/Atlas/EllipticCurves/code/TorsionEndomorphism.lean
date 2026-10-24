/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/TorsionEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import sympy.atlas.v1.Atlas.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies

universe u

namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

/-- The multiplication-by-`n` endomorphism `[n]` on the group of points of a Weierstrass
curve, packaged as an additive group homomorphism `W.Point →+ W.Point`. -/
def multiplicationByN (W : WeierstrassCurve.Affine F) (n : ℤ) : W.Point →+ W.Point :=
  zsmulAddGroupHom n

/-- The `n`-torsion subgroup `E[n]` of a Weierstrass curve, defined as the kernel of the
multiplication-by-`n` homomorphism. -/
def torsionSubgroup (W : WeierstrassCurve.Affine F) (n : ℤ) : AddSubgroup W.Point :=
  (multiplicationByN W n).ker

/-- Any additive group homomorphism between point groups of Weierstrass curves preserves
the `n`-torsion subgroup. -/
theorem map_mem_torsionSubgroup {W₁ W₂ : WeierstrassCurve.Affine F}
    (φ : W₁.Point →+ W₂.Point) (n : ℤ) (P : W₁.Point)
    (hP : P ∈ torsionSubgroup W₁ n) :
    φ P ∈ torsionSubgroup W₂ n := by
  simp only [mem_torsionSubgroup] at hP ⊢
  rw [← φ.map_zsmul, hP, map_zero]

/-- A Weierstrass curve `W` over a field of characteristic `p` is ordinary if its
`p`-torsion `E[p]` is isomorphic to `ℤ/pℤ` (cf. Definition 6.2 of Sutherland). -/
def IsOrdinary (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p] [Fact (Nat.Prime p)] :
    Prop :=
  Nonempty ((torsionSubgroup W (p : ℤ)) ≃+ ZMod p)

/-- A Weierstrass curve `W` over a field of characteristic `p` is supersingular if its
`p`-torsion `E[p]` is trivial (cf. Definition 6.2 of Sutherland). -/
def IsSupersingular (W : WeierstrassCurve.Affine F) (p : ℕ) [CharP F p]
    [Fact (Nat.Prime p)] : Prop :=
  torsionSubgroup W (p : ℤ) = ⊥

/-- The `n`-torsion subgroup `E(K)[n]` of an elliptic curve `E/k` after base change to a
field extension `K`, defined as the torsion subgroup of the projective point group. -/
def EllipticCurve.torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) : AddSubgroup (E.map (algebraMap k K)).toProjective.Point :=
  AddSubgroup.torsionBy (E.map (algebraMap k K)).toProjective.Point n

/-- Membership characterisation: a point `P ∈ E(K)` lies in `E(K)[n]` iff `n • P = 0`. -/
@[simp]
lemma EllipticCurve.mem_torsionSubgroup
    (k : Type*) [Field k]
    (E : WeierstrassCurve k) [E.IsElliptic]
    (K : Type*) [Field K] [Algebra k K]
    (n : ℤ) (P : (E.map (algebraMap k K)).toProjective.Point) :
    P ∈ EllipticCurve.torsionSubgroup k E K n ↔ n • P = 0 := by
  simp [EllipticCurve.torsionSubgroup]

/-- Definition 6.13: the endomorphism ring `End(E) = Hom(E, E)` as the additive monoid of
endomorphisms of `E.Point`, with multiplication given by composition. -/
abbrev EndRing : Type u :=
  AddMonoid.End E.Point

/-- Ring structure on `EndRing E`, inherited from `AddMonoid.End`. -/
instance : Ring (EndRing E) := AddMonoid.End.instRing

variable {E}

/-- The canonical ring homomorphism `ℤ → End(E)` sending `n` to `[n]`. -/
noncomputable def intToEndRingHom : ℤ →+* EndRing E :=
  Int.castRingHom (EndRing E)

/-- Existence of an isogeny representing `[1] - α`, used to package the trace
construction underlying Definition 6.17. -/
noncomputable def Isogeny.traceAux
    (α : Isogeny E E)
    (oneMinusAlpha : Isogeny E E)
    (_ : oneMinusAlpha.toAddMonoidHom =
      multiplicationByN E 1 - α.toAddMonoidHom) : ℤ :=
  1 + (α.degree : ℤ) - (oneMinusAlpha.degree : ℤ)

/-- Rephrasing of Lemma 6.16 in terms of `traceAux`: `α + α̂ = [traceAux α (1-α)]`. -/
end Definition617

section Theorem618

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Convenience abbreviation `trace'` for `Isogeny.trace`, used to state Theorem 6.18. -/
end Theorem618

section Lemma619

open WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]
variable {E : WeierstrassCurve.Affine F}

/-- Two endomorphisms `α, β` of `E` agree on `n`-torsion iff their underlying maps match
on `E[n]`. This is the predicate denoted `αₙ = βₙ` in Lemma 6.19. -/
def Isogeny.agreeOnTorsion (α β : Isogeny E E) (n : ℤ) : Prop :=
  ∀ (P : E.Point), P ∈ torsionSubgroup E n → α.toAddMonoidHom P = β.toAddMonoidHom P

/-- Cauchy-style interpolation for endomorphisms: if `α` and `β` agree on `E[n]` for a
sufficiently large `n` coprime to the characteristic and to both degrees, then globally
either `α = β` or `α = -β`. -/
end Lemma619
