/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/AlgebraNotes.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.ZMod.Any_Nonempty_ZModPow
import Theorem.Ideal.Any_And_Le.of.Ne_Top
import Theorem.Fin.Any_EqToBilin'AndIsSymm.is.IsSymmToMatrix'
import Theorem.Nat.IsPGroupG.is.CardG.eq.Pow
import Theorem.Set.SMul.of.In_SMul
import Theorem.Int.OrderOf.eq.ZeroAndInjectiveOrOrderOf.Gt_0AndCard.eq.OrderOf
import Theorem.Fin.AddFinrankS.eq.Finrank
import Theorem.Submodule.Eq_Top.of.Eq_Bot.AddFinrankS.eq.Finrank
import Theorem.Matrix.In_SpectrumF.is.IsRootCharpoly
import Theorem.Nat.Any_Eq_AddSquareS.is.All_Even_PadicValNat
import Theorem.Rat.IsCyclicG
import Theorem.Fin.Nonempty_OrthonormalBasis_Fin_FinrankVV
import Theorem.Nat.CardG.eq.MulIndexCard
import Theorem.Matrix.Rank
import Theorem.Int.IsNoetherianRing.is.All_IsNoetherian
import Theorem.Polynomial.IsNoetherianRingPolynomial
import Theorem.Set.Normal.is.All_EqSSMul
import Theorem.Nat.Nontrivial_CenterG.of.IsPGroupG
import Theorem.Int.Any_Nonempty.is.Any_And_Ne_0AndNe_1
import Lemma.Nat.Surjective_Mk'AndEqKer_Mk'
import Theorem.Matrix.MulMulStar.eq.Diagonal.of.IsStarNormal
import Def.v1.Atlas.AlgebraNotes.code.AdjointOperators
import Theorem.Matrix.inner.eq.inner_Adjoint
import Theorem.Representation.FinrankHomG.eq.Nonempty_Equiv
import Theorem.Ideal.IsMaximal.is.Any_Eq_VanishingIdeal
import Theorem.Submodule.All_EqTmul0AndEqTmul0.All_EqTmulSMulAndEqTmulSMulAndAll_EqSpanTop
import Theorem.Fin.IsSemisimple.of.SquarefreeCharpoly
import Theorem.Matrix.MulMul_ConstVAdd.eq.ConstVAdd
import Theorem.Nat.Associated.is.Any_Eq_Mul
import Theorem.Matrix.FiniteDimensionalAndFinrank.eq.MulFinrankS
import Theorem.Matrix.IsSeparable.is.All_SeparableMinpoly
import Theorem.Matrix.Card.le.Finrank
import Theorem.Nat.Card.eq.Sum_CardOrbit
import Theorem.Nat.Eq_1.of.All_Eq_Mul
import Theorem.Ideal.All_PrimeAndAssociatedProdNormalizedFactors.of.Ne_Bot
import Theorem.Ideal.IsMaximal.is.Ne_TopAndAll_EqOrEq_Top
import Theorem.Real.Plane.eq.AddLinearIsometryEquiv
import Theorem.MvPolynomial.All_Eq.Unique
import Theorem.Nat.EqMulS
import Theorem.MonoidAlgebra.Any_IsCompl
import Theorem.Int.Eq_1.of.IsUnit
import Lemma.Matrix.A.eq.SubMulS
import Theorem.Nat.Any_EqCardPow_FactorizationCard.All_EqToSubgroupMapToSubgroupAndAll_All_Any_Le_MapToSubgroupAndCard.dvd.DivCardPow_FactorizationCardAndCard
import Theorem.Fin.IsConj.is.CycleType
import Theorem.Submodule.Any_Eq.is.LinearIndependentAndSpan.eq.Top
import Def.v1.Atlas.AlgebraNotes.code.Characters
import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebra
import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraFacts
import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraGoals
import Def.v1.Atlas.AlgebraNotes.code.CorrespondenceTheorem
import Def.v1.Atlas.AlgebraNotes.code.DehnInvariant.Part2
import Def.v1.Atlas.AlgebraNotes.code.Diagonalization
import Def.v1.Atlas.AlgebraNotes.code.DiscreteGroups
import Theorem.v1.Atlas.AlgebraNotes.code.DomainHierarchy
import Theorem.v1.Atlas.AlgebraNotes.code.Factorization
import Theorem.v1.Atlas.AlgebraNotes.code.FieldExtensions
import Def.v1.Atlas.AlgebraNotes.code.FieldExtensionsGaloisRemaining
import Def.v1.Atlas.AlgebraNotes.code.GaloisCorrespondence
import Abbrev.v1.Atlas.AlgebraNotes.code.GaloisTheory
import Theorem.v1.Atlas.AlgebraNotes.code.GoalCoverage
import Theorem.v1.Atlas.AlgebraNotes.code.GoalCoverageRemaining
import Def.v1.Atlas.AlgebraNotes.code.GroupActions
import Def.v1.Atlas.AlgebraNotes.code.GroupHomomorphisms
import Theorem.v1.Atlas.AlgebraNotes.code.Groups
import Def.v1.Atlas.AlgebraNotes.code.IdealFactorization.Part2
import Instance.v1.Atlas.AlgebraNotes.code.Ideals
import Theorem.Ideal.Span.eq.SpanGcd
import Def.v1.Atlas.AlgebraNotes.code.Isometries
import Theorem.v1.Atlas.AlgebraNotes.code.JordanCyclicBasis
import Def.v1.Atlas.AlgebraNotes.code.JordanForm
import Theorem.v1.Atlas.AlgebraNotes.code.NoetherianGoals
import Def.v1.Atlas.AlgebraNotes.code.OrthogonalGroup
import Def.v1.Atlas.AlgebraNotes.code.Polynomials
import Theorem.v1.Atlas.AlgebraNotes.code.ProductGroups
import Abbrev.v1.Atlas.AlgebraNotes.code.QuadraticFields
import Def.v1.Atlas.AlgebraNotes.code.RepresentationTheory
import Theorem.v1.Atlas.AlgebraNotes.code.Rings
import Def.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part5
import Def.v1.Atlas.AlgebraNotes.code.SylowTheorems
import Def.v1.Atlas.AlgebraNotes.code.SymmetricGroups
import Theorem.v1.Atlas.AlgebraNotes.code.SymmetryGroups
import Theorem.v1.Atlas.AlgebraNotes.code.VectorSpaces


