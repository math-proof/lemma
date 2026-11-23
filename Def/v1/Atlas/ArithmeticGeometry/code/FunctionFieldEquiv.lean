/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FunctionFieldEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part10
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.CurveTheory
public import Instance.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv.Part3

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

attribute [instance] SmProjCurve.isIntegral SmProjCurve.isProper SmProjCurve.isSmooth

def SmProjCurve.algebraMapHom (C : SmProjCurve k) :
    CommRingCat.of k ⟶ C.toScheme.functionField := by
  haveI : IrreducibleSpace C.toScheme := irreducibleSpace_of_isIntegral C.toScheme
  haveI : Nonempty C.toScheme := IsIntegral.nonempty
  haveI : Nonempty (⊤ : C.toScheme.Opens) := ⟨⟨IsIntegral.nonempty.some, trivial⟩⟩
  exact (Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMorphism.appTop ≫
    C.toScheme.germToFunctionField ⊤

end Thm19_2
end ArithmeticGeometry
end
