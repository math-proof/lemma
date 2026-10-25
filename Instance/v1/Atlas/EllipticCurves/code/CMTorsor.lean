/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part3


namespace FieldNormTrace

section Quadratic

variable {D : ℤ}

namespace FractionalOIdeal

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

open FractionalIdeal

/-- `ℤ√d` is free as a `ℤ`-module, via the equivalence with `Fin 2 → ℤ`. -/
noncomputable instance instModuleFreeZsqrtd : Module.Free ℤ (ℤ√d) :=
  Module.Free.of_equiv (zsqrtdLinearEquivFin2 d).symm

/-- `ℤ√d` is finitely generated as a `ℤ`-module (in fact rank 2). -/
noncomputable instance instModuleFiniteZsqrtd : Module.Finite ℤ (ℤ√d) :=
  Module.Finite.equiv (zsqrtdLinearEquivFin2 d).symm

end FractionalOIdeal
end Quadratic
end FieldNormTrace
