/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part7
public import Theorem.Rat.EqProjectToH.of.Given
public import Theorem.Ideal.IsHomogeneous_AugmentationIdealGraded
public import Instance.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part2
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Equiv
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Invariant.Basic
public import Structure.v1.Atlas.LieGroups.code.CSTTheorem

@[expose] public section

noncomputable section

universe u

attribute [instance] CSTPartIIData.instGroup CSTPartIIData.instFintype

attribute [instance] CSTPartIIData.instDecEq

attribute [instance] CSTPartIIData.instR₀AddCommGroup CSTPartIIData.instR₀Module

attribute [instance] CSTPartIIData.instR₀FiniteDimensional

def CSTPartIIData.polyRep (cst : CSTPartIIData) :
    Representation ℂ cst.G (MvPolynomial (Fin cst.n) ℂ) :=
  polyRepresentation cst.algAct

variable (cst : CSTPartIIData)

def qIntPoly (d : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d, Polynomial.X ^ i

end
