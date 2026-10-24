/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/GoalCoverageRemaining.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraNotes.code.GoalCoverage
import sympy.atlas.v1.Atlas.AlgebraNotes.code.AdjointOperators
import Lemma.Matrix.inner.eq.inner_Adjoint
import Lemma.Matrix.A.eq.SubMulS
import Lemma.MonoidAlgebra.Any_IsCompl
import Lemma.Representation.FinrankHomG.eq.Nonempty_Equiv
import Lemma.Ideal.IsMaximal.is.Any_Eq_VanishingIdeal
import Lemma.Nat.Associated.is.Any_Eq_Mul
import Lemma.Matrix.Card.le.Finrank
import Lemma.Matrix.IsSeparable.is.All_SeparableMinpoly
import sympy.atlas.v1.Atlas.AlgebraNotes.code.SimpleGroups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.RepresentationTheory
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Characters
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraGoals
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraFacts
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CommutativeAlgebra
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Factorization
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GaloisTheory
import sympy.atlas.v1.Atlas.AlgebraNotes.code.FieldExtensionsGaloisRemaining

noncomputable section
