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
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Instance.v1.Atlas.EllipticCurves.code.TorsionEndomorphism
universe u


namespace WeierstrassCurve.Affine

variable {F : Type u} [Field F] [DecidableEq F]

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

end Lemma619
