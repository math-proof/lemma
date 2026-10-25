/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DegreeAdditivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Length
import Mathlib.RingTheory.OrderOfVanishing
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Def.v1.Atlas.AlgebraicGeometryI.code.DegreeAdditivity


noncomputable section

open Submodule

namespace DegreeAdditivity

/-- Data of a short exact sequence of `R`-modules `0 → N → M → P → 0`, suitable as a defining
relation in `K₀(R)`. -/
structure K0SESRelation (R : Type*) [Ring R] where
  N : Type*
  M : Type*
  P : Type*
  [instN : AddCommGroup N]
  [modN : Module R N]
  [instM : AddCommGroup M]
  [modM : Module R M]
  [instP : AddCommGroup P]
  [modP : Module R P]
  f : N →ₗ[R] M
  g : M →ₗ[R] P
  f_inj : Function.Injective f
  g_surj : Function.Surjective g
  exact : Function.Exact f g

end DegreeAdditivity
end
