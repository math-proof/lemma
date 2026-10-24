/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/AlgebraNotes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Lemma.ZMod.Any_Nonempty_ZModPow
import Lemma.Ideal.Any_And_Le.of.Ne_Top
import Lemma.Fin.Any_EqToBilin'AndIsSymm.is.IsSymmToMatrix'
import Lemma.Nat.IsPGroupG.is.CardG.eq.Pow
import Lemma.Set.SMul.of.In_SMul
import Lemma.Int.OrderOf.eq.ZeroAndInjectiveOrOrderOf.Gt_0AndCard.eq.OrderOf
import Lemma.Fin.AddFinrankS.eq.Finrank
import Lemma.Submodule.Eq_Top.of.Eq_Bot.AddFinrankS.eq.Finrank
import Lemma.Matrix.In_SpectrumF.is.IsRootCharpoly
import Lemma.Nat.Any_Eq_AddSquareS.is.All_Even_PadicValNat
import Lemma.Rat.IsCyclicG
import Lemma.Fin.Nonempty_OrthonormalBasis_Fin_FinrankVV
import Lemma.Nat.CardG.eq.MulIndexCard
import Lemma.Matrix.Rank
import Lemma.Int.IsNoetherianRing.is.All_IsNoetherian
import Lemma.Polynomial.IsNoetherianRingPolynomial
import Lemma.Set.Normal.is.All_EqSSMul
import Lemma.Nat.Nontrivial_CenterG.of.IsPGroupG
import Lemma.Int.Any_Nonempty.is.Any_And_Ne_0AndNe_1
import Lemma.Nat.Surjective_Mk'AndEqKer_Mk'
import Lemma.Matrix.MulMulStar.eq.Diagonal.of.IsStarNormal
import sympy.atlas.v1.Atlas.AlgebraNotes.code.AdjointOperators
import Lemma.Matrix.inner.eq.inner_Adjoint
import Lemma.Representation.FinrankHomG.eq.Nonempty_Equiv
import Lemma.Ideal.IsMaximal.is.Any_Eq_VanishingIdeal
import Lemma.Submodule.All_EqTmul0AndEqTmul0.All_EqTmulSMulAndEqTmulSMulAndAll_EqSpanTop
import Lemma.Fin.IsSemisimple.of.SquarefreeCharpoly
import Lemma.Matrix.MulMul_ConstVAdd.eq.ConstVAdd
import Lemma.Nat.Associated.is.Any_Eq_Mul
import Lemma.Matrix.FiniteDimensionalAndFinrank.eq.MulFinrankS
import Lemma.Matrix.IsSeparable.is.All_SeparableMinpoly
import Lemma.Matrix.Card.le.Finrank
import Lemma.Nat.Card.eq.Sum_CardOrbit
import Lemma.Nat.Eq_1.of.All_Eq_Mul
import Lemma.Ideal.All_PrimeAndAssociatedProdNormalizedFactors.of.Ne_Bot
import Lemma.Ideal.IsMaximal.is.Ne_TopAndAll_EqOrEq_Top
import Lemma.Real.Plane.eq.AddLinearIsometryEquiv
import Lemma.MvPolynomial.All_Eq.Unique
import Lemma.Nat.EqMulS
import Lemma.MonoidAlgebra.Any_IsCompl
import Lemma.Int.Eq_1.of.IsUnit
import Lemma.Matrix.A.eq.SubMulS
import Lemma.Nat.Any_EqCardPow_FactorizationCard.All_EqToSubgroupMapToSubgroupAndAll_All_Any_Le_MapToSubgroupAndCard.dvd.DivCardPow_FactorizationCardAndCard
import Lemma.Fin.IsConj.is.CycleType
import Lemma.Submodule.Any_Eq.is.LinearIndependentAndSpan.eq.Top
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Characters
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CommutativeAlgebra
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraFacts
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraGoals
import sympy.atlas.v1.Atlas.AlgebraNotes.code.CorrespondenceTheorem
import sympy.atlas.v1.Atlas.AlgebraNotes.code.DehnInvariant
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Diagonalization
import sympy.atlas.v1.Atlas.AlgebraNotes.code.DiscreteGroups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.DomainHierarchy
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Factorization
import sympy.atlas.v1.Atlas.AlgebraNotes.code.FieldExtensions
import sympy.atlas.v1.Atlas.AlgebraNotes.code.FieldExtensionsGaloisRemaining
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GaloisCorrespondence
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GaloisTheory
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GoalCoverage
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GoalCoverageRemaining
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GroupActions
import sympy.atlas.v1.Atlas.AlgebraNotes.code.GroupHomomorphisms
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Groups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.IdealFactorization
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Ideals
import Lemma.Ideal.Span.eq.SpanGcd
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Isometries
import sympy.atlas.v1.Atlas.AlgebraNotes.code.JordanCyclicBasis
import sympy.atlas.v1.Atlas.AlgebraNotes.code.JordanForm
import sympy.atlas.v1.Atlas.AlgebraNotes.code.NoetherianGoals
import sympy.atlas.v1.Atlas.AlgebraNotes.code.OrthogonalGroup
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Polynomials
import sympy.atlas.v1.Atlas.AlgebraNotes.code.ProductGroups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.QuadraticFields
import sympy.atlas.v1.Atlas.AlgebraNotes.code.RepresentationTheory
import sympy.atlas.v1.Atlas.AlgebraNotes.code.Rings
import sympy.atlas.v1.Atlas.AlgebraNotes.code.SimpleGroups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.SylowTheorems
import sympy.atlas.v1.Atlas.AlgebraNotes.code.SymmetricGroups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.SymmetryGroups
import sympy.atlas.v1.Atlas.AlgebraNotes.code.VectorSpaces
