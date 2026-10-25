/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ChevalleyRestriction.Part7
import Lemma.Rat.EqProjectToH.of.Given
import Lemma.Ideal.IsHomogeneousAugmentationIdealGraded
import Instance.v1.Atlas.LieGroups.code.SyzygiesKoszul.Part2
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Invariant.Basic
import Structure.v1.Atlas.LieGroups.code.CSTTheorem


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
