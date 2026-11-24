module
public import Theorem.ZMod.Any_Nonempty_ZModPow
public import Theorem.Ideal.Any_And_Le.of.Ne_Top
public import Theorem.Fin.Any_EqToBilin'AndIsSymm.is.IsSymmToMatrix'
public import Theorem.Nat.IsPGroupG.is.CardG.eq.Pow
public import Theorem.Set.SMul.of.In_SMul
public import Theorem.Int.OrderOf.eq.ZeroAndInjectiveOrOrderOf.Gt_0AndCard.eq.OrderOf
public import Theorem.Fin.AddFinrankS.eq.Finrank
public import Theorem.Submodule.Eq_Top.of.Eq_Bot.AddFinrankS.eq.Finrank
public import Theorem.Matrix.In_SpectrumF.is.IsRootCharpoly
public import Theorem.Nat.Any_Eq_AddSquareS.is.All_Even_PadicValNat
public import Theorem.Rat.IsCyclicG
public import Theorem.Fin.Nonempty_OrthonormalBasis_Fin_FinrankVV
public import Theorem.Nat.CardG.eq.MulIndexCard
public import Theorem.Matrix.Rank
public import Theorem.Int.IsNoetherianRing.is.All_IsNoetherian
public import Theorem.Polynomial.IsNoetherianRingPolynomial
public import Theorem.Set.Normal.is.All_EqSSMul
public import Theorem.Nat.Nontrivial_CenterG.of.IsPGroupG
public import Theorem.Int.Any_Nonempty.is.Any_And_Ne_0AndNe_1
public import Theorem.Nat.Surjective_Mk'AndEqKer_Mk'
public import Theorem.Matrix.MulMulStar.eq.Diagonal.of.IsStarNormal
public import Def.v1.Atlas.AlgebraNotes.code.AdjointOperators
public import Theorem.Matrix.inner.eq.inner_Adjoint
public import Theorem.Representation.FinrankHomG.eq.Nonempty_Equiv
public import Theorem.Ideal.IsMaximal.is.Any_Eq_VanishingIdeal
public import Theorem.Submodule.All_EqTmul0AndEqTmul0.All_EqTmulSMulAndEqTmulSMulAndAll_EqSpanTop
public import Theorem.Fin.IsSemisimple.of.SquarefreeCharpoly
public import Theorem.Matrix.MulMul_ConstVAdd.eq.ConstVAdd
public import Theorem.Nat.Associated.is.Any_Eq_Mul
public import Theorem.Matrix.FiniteDimensionalAndFinrank.eq.MulFinrankS
public import Theorem.Matrix.IsSeparable.is.All_SeparableMinpoly
public import Theorem.Matrix.Card.le.Finrank
public import Theorem.Nat.Card.eq.Sum_CardOrbit
public import Theorem.Nat.Eq_1.of.All_Eq_Mul
public import Theorem.Ideal.All_PrimeAndAssociatedProdNormalizedFactors.of.Ne_Bot
public import Theorem.Ideal.IsMaximal.is.Ne_TopAndAll_EqOrEq_Top
public import Theorem.Real.Plane.eq.AddLinearIsometryEquiv
public import Theorem.MvPolynomial.All_Eq.Unique
public import Theorem.Nat.EqMulS
public import Theorem.MonoidAlgebra.Any_IsCompl
public import Theorem.Int.Eq_1.of.IsUnit
public import Theorem.Matrix.A.eq.SubMulS
public import Theorem.Nat.Any_EqCardPow_FactorizationCard.All_EqToSubgroupMapToSubgroupAndAll_All_Any_Le_MapToSubgroupAndCard.dvd.DivCardPow_FactorizationCardAndCard
public import Theorem.Fin.IsConj.is.CycleType
public import Theorem.Submodule.Any_Eq.is.LinearIndependentAndSpan.eq.Top
public import Def.v1.Atlas.AlgebraNotes.code.Characters
public import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebra
public import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraFacts
public import Theorem.v1.Atlas.AlgebraNotes.code.CommutativeAlgebraGoals
public import Def.v1.Atlas.AlgebraNotes.code.CorrespondenceTheorem
public import Def.v1.Atlas.AlgebraNotes.code.DehnInvariant.Part2
public import Def.v1.Atlas.AlgebraNotes.code.Diagonalization
public import Def.v1.Atlas.AlgebraNotes.code.DiscreteGroups
public import Theorem.v1.Atlas.AlgebraNotes.code.DomainHierarchy
public import Theorem.v1.Atlas.AlgebraNotes.code.Factorization
public import Theorem.v1.Atlas.AlgebraNotes.code.FieldExtensions
public import Def.v1.Atlas.AlgebraNotes.code.FieldExtensionsGaloisRemaining
public import Def.v1.Atlas.AlgebraNotes.code.GaloisCorrespondence
public import Abbrev.v1.Atlas.AlgebraNotes.code.GaloisTheory
public import Theorem.v1.Atlas.AlgebraNotes.code.GoalCoverage
public import Theorem.v1.Atlas.AlgebraNotes.code.GoalCoverageRemaining
public import Def.v1.Atlas.AlgebraNotes.code.GroupActions
public import Def.v1.Atlas.AlgebraNotes.code.GroupHomomorphisms
public import Theorem.v1.Atlas.AlgebraNotes.code.Groups
public import Def.v1.Atlas.AlgebraNotes.code.IdealFactorization.Part2
public import Instance.v1.Atlas.AlgebraNotes.code.Ideals
public import Theorem.Ideal.Span.eq.SpanGcd
public import Def.v1.Atlas.AlgebraNotes.code.Isometries
public import Theorem.v1.Atlas.AlgebraNotes.code.JordanCyclicBasis
public import Def.v1.Atlas.AlgebraNotes.code.JordanForm
public import Theorem.v1.Atlas.AlgebraNotes.code.NoetherianGoals
public import Def.v1.Atlas.AlgebraNotes.code.OrthogonalGroup
public import Def.v1.Atlas.AlgebraNotes.code.Polynomials
public import Theorem.v1.Atlas.AlgebraNotes.code.ProductGroups
public import Abbrev.v1.Atlas.AlgebraNotes.code.QuadraticFields
public import Def.v1.Atlas.AlgebraNotes.code.RepresentationTheory
public import Theorem.v1.Atlas.AlgebraNotes.code.Rings
public import Def.v1.Atlas.AlgebraNotes.code.SimpleGroups.Part5
public import Def.v1.Atlas.AlgebraNotes.code.SylowTheorems
public import Def.v1.Atlas.AlgebraNotes.code.SymmetricGroups
public import Theorem.v1.Atlas.AlgebraNotes.code.SymmetryGroups
public import Theorem.v1.Atlas.AlgebraNotes.code.VectorSpaces


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/AlgebraNotes.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

