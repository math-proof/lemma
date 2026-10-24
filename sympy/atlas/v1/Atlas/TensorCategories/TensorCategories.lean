/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/TensorCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.AlgebraInCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.AlgebrasInCategories
import Lemma.Category.Atlas.v1.TensorCategories.code.BasicMonoidalDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.Bimodule
import Lemma.Category.Atlas.v1.TensorCategories.code.Ch1Theorems
import Lemma.Category.Atlas.v1.TensorCategories.code.ChevalleyProperty
import Lemma.Category.Atlas.v1.TensorCategories.code.CoalgebraBialgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.ComoduleDuals
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_13_7
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_15_2
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_15_9
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_22_6
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_48_3
import Lemma.Category.Atlas.v1.TensorCategories.code.DeligneTensorProduct
import Lemma.Category.Atlas.v1.TensorCategories.code.DualCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.Ext1UnitVanishing
import Lemma.Category.Atlas.v1.TensorCategories.code.FPdimProps
import Lemma.Category.Atlas.v1.TensorCategories.code.FiberFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.FiberFunctorEnd
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingAlgebraLocalRing
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingLemmaInstance
import Lemma.Category.Atlas.v1.TensorCategories.code.FittingLemmaLocalEnd
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckFusionRingInstance
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckModuleIrreducible
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRing
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GroupoidMultitensor
import Lemma.Category.Atlas.v1.TensorCategories.code.HigherDerivation
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebraAntiHom
import Lemma.Category.Atlas.v1.TensorCategories.code.InternalHom
import Lemma.Category.Atlas.v1.TensorCategories.code.InvertibleObjects
import Lemma.Category.Atlas.v1.TensorCategories.code.K0Bimodule
import Lemma.Category.Atlas.v1.TensorCategories.code.Lemma285
import Lemma.Category.Atlas.v1.TensorCategories.code.Lemma_1_30_2
import Lemma.Category.Atlas.v1.TensorCategories.code.MacLaneCoherence
import Lemma.Category.Atlas.v1.TensorCategories.code.MacLaneStrictness
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleFunctorDefs
import Lemma.Category.Atlas.v1.TensorCategories.code.ModuleRigidityCompat
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorProps
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalFunctorsCohomology
import Lemma.Category.Atlas.v1.TensorCategories.code.MonoidalStructuresGraded
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Lemma.Category.Atlas.v1.TensorCategories.code.ProjectiveCoverInfra
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_27_1
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_2_4
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_45_2
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_45_5
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_6_4
import Lemma.Category.Atlas.v1.TensorCategories.code.QBinomial
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumGroupGeneral
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2Concrete
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2Instance
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctorProjective
import Lemma.Category.Atlas.v1.TensorCategories.code.ReductiveGroup
import Lemma.Category.Atlas.v1.TensorCategories.code.RegularElement
import Lemma.Category.Atlas.v1.TensorCategories.code.RegularObject
import Lemma.Category.Atlas.v1.TensorCategories.code.RigidMonoidalDuality
import Lemma.Category.Atlas.v1.TensorCategories.code.SemisimpleMultitensor
import Lemma.Category.Atlas.v1.TensorCategories.code.SurjectiveTensorFunctor
import Lemma.Category.Atlas.v1.TensorCategories.code.SweedlerHopfInstance
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorExact
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorNondegen.DualZero
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorNondegen.EvalCoevalArg
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorNondegen.ZeroTensorZero
import Lemma.Category.Atlas.v1.TensorCategories.code.TraceNonzero
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitProjectiveSemisimple
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.EvalCoeval
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.TensorExactness
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.UnitSimple
import Lemma.Category.Atlas.v1.TensorCategories.code.VecCategoricalFusionData
import Lemma.Category.Atlas.v1.TensorCategories.code.VecDualMapBridge
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Lemma.Category.Atlas.v1.TensorCategories.code.VecPivotal.SphericalInstance
import Lemma.Category.Atlas.v1.TensorCategories.code.VecPivotalConcrete
import Lemma.Category.Atlas.v1.TensorCategories.code.VecSemisimple
import Lemma.Category.Atlas.v1.TensorCategories.code.VecSphericalConcrete
import Lemma.Category.Atlas.v1.TensorCategories.code.ZPlusModules
import sympy.atlas.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs
-- import Formalization.AlgebrasInCategoriesDefsBatch  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.Assembly  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.Injective  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.RankEquality  -- commented out: conflicts with other imports
-- import Formalization.BasedRings  -- commented out: conflicts with other imports
-- import Formalization.BasedRingsGeneral  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.BasicMonoidalDefs
import sympy.atlas.v1.Atlas.TensorCategories.code.BialgebraReconstruction
import sympy.atlas.v1.Atlas.TensorCategories.code.Bimodule
import sympy.atlas.v1.Atlas.TensorCategories.code.BuildStubAudit
import sympy.atlas.v1.Atlas.TensorCategories.code.BuildVerified
-- import Formalization.CartierKostant.Axioms  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.CommHopfFunGroup  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.Theorems  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.CategoricalDimension
-- import Formalization.CategoricalFreeness  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Ch1Theorems
import sympy.atlas.v1.Atlas.TensorCategories.code.ChevalleyProperty
-- import Formalization.ChevalleyTheorem -- commented out: Mathlib API change (IsSemisimpleModule.jacobson_eq_bot)
import sympy.atlas.v1.Atlas.TensorCategories.code.CoalgebraBialgebra
-- import Formalization.CocommutativeMonoidAlgebra  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.ComoduleDuals
-- import Formalization.ConcreteInstances  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.ConcreteInstancesModule
-- import Formalization.ConcreteModuleCategories  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.CoradicalFiltration
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_13_4
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_13_7
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_15_2
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_15_9
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_22_6
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_29_5
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_45_11
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_1_45_16
import Lemma.Category.Atlas.v1.TensorCategories.code.Corollary_2_7_2
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleProjectives
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingHom
import Lemma.Category.Atlas.v1.TensorCategories.code.Lemma_2_13_2
import Lemma.Category.Atlas.v1.TensorCategories.code.Lemma_2_13_3
import Lemma.Category.Atlas.v1.TensorCategories.code.Lemma_2_8_5
import Lemma.Category.Atlas.v1.TensorCategories.code.Prop_1_45_10
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_34_7
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_45_15
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_1_48_2
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_2_14_14
import Lemma.Category.Atlas.v1.TensorCategories.code.Proposition_2_7_7
import Lemma.Category.Atlas.v1.TensorCategories.code.RegularObjectAbsorption
import Lemma.Category.Atlas.v1.TensorCategories.code.TensorProjective.Proposition_1_13_6
import Lemma.Category.Atlas.v1.TensorCategories.code.Theorem_1_15_8
import Lemma.Category.Atlas.v1.TensorCategories.code.Theorem_1_25_2
import Lemma.Category.Atlas.v1.TensorCategories.code.Theorem_2_14_11
-- import Formalization.Corollary_1_29_7  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_31_5
-- import Formalization.Corollary_1_43_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_43_6  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Corollary_1_48_3
-- import Formalization.Corollary_1_50_3  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_50_4  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_51_3  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_51_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_2_10_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_2_14_9  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_1_15_4
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_1_18_1
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_1_18_2
-- import Formalization.Definition_1_22_2  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_1_34_1
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_1_45_7
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_1_46_1
-- import Formalization.Definition_1_52_1  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_52_6  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_5_1  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_2_1_6
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_2_3_1
-- import Formalization.Definition_2_5_4  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_2_9_1
import sympy.atlas.v1.Atlas.TensorCategories.code.Definition_2_9_18_ExactAlgebra
-- import Formalization.Definition_2_9_21  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_22  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_24  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.DeligneTensorProduct
import sympy.atlas.v1.Atlas.TensorCategories.code.DeligneTensorProductDef
import sympy.atlas.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import sympy.atlas.v1.Atlas.TensorCategories.code.DirectSumModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.DirectSumModuleCategoryDef
-- import Formalization.DistinguishedInvertible  -- commented out: conflicts with other imports
-- import Formalization.DrinfeldCenter  -- commented out: conflicts with other imports
-- import Formalization.DualCatDefs  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.DualCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.DualCoherenceBridge
import sympy.atlas.v1.Atlas.TensorCategories.code.DualDefinitions
import sympy.atlas.v1.Atlas.TensorCategories.code.EndTensorProduct
-- import Formalization.ExactAlgebra  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCriteria
import sympy.atlas.v1.Atlas.TensorCategories.code.Ext1UnitVanishing
import sympy.atlas.v1.Atlas.TensorCategories.code.FPdimCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.FPdimCosine
import sympy.atlas.v1.Atlas.TensorCategories.code.FPdimFunctor
import sympy.atlas.v1.Atlas.TensorCategories.code.FPdimProps
import sympy.atlas.v1.Atlas.TensorCategories.code.FiberFunctor
import sympy.atlas.v1.Atlas.TensorCategories.code.FiberFunctorEnd
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteCategoryDef
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteTensorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.FittingAlgebraLocalRing
import sympy.atlas.v1.Atlas.TensorCategories.code.FittingLemmaInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.FittingLemmaLocalEnd
import sympy.atlas.v1.Atlas.TensorCategories.code.FrobeniusPerron
import sympy.atlas.v1.Atlas.TensorCategories.code.GradedVec
import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckModuleIrreducible
import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckRing
import sympy.atlas.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical
import sympy.atlas.v1.Atlas.TensorCategories.code.GroupoidMultitensor
import sympy.atlas.v1.Atlas.TensorCategories.code.HigherDerivation
import sympy.atlas.v1.Atlas.TensorCategories.code.HomExactImpliesExact
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebraAntiHom
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebraExamples
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebraRep
-- import Formalization.HopfAlgebraRigid  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import sympy.atlas.v1.Atlas.TensorCategories.code.Instances.VecFiniteTensorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.IntegralCategories
-- import Formalization.IntegralsCartanMatrix  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.IntegralsClean
-- import Formalization.IntegralsDefs  -- commented out: conflicts with other imports
-- import Formalization.IntegralsProps  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.InternalHom
-- import Formalization.InternalHomEssSurjInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFaithfulInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFullInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFunctor  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.InvertibleObjects
import sympy.atlas.v1.Atlas.TensorCategories.code.K0Bimodule
import sympy.atlas.v1.Atlas.TensorCategories.code.Lemma285
import sympy.atlas.v1.Atlas.TensorCategories.code.Lemma_1_30_2
-- import Formalization.Lemma_1_33_2  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Lemma_1_51_1
-- import Formalization.Lemma_2_14_10  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Lemma_2_14_7
-- import Formalization.Lemma_2_9_12  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.LocalEndRingsInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.LocallyFiniteDefs
import sympy.atlas.v1.Atlas.TensorCategories.code.MacLaneCoherence
import sympy.atlas.v1.Atlas.TensorCategories.code.MacLaneStrictness
-- import Formalization.MfStarAlgebra  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory.Theorem2112
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory.Theorem2116
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategoryDecomp
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategoryEquiv
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategoryMultitensor
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctor
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctorAbelianDefs
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctorCategoryAbelianInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleFunctorFinite
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleOverAlgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleRigidityCompat
-- import Formalization.MonoidalCategoryDef  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalFunctorDef
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalFunctorProps
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology
import sympy.atlas.v1.Atlas.TensorCategories.code.MonoidalStructuresGraded
-- import Formalization.MonoidalUnitProperties  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.MoritaEquivalence
-- import Formalization.MultifusionSemisimple  -- commented out: conflicts with other imports
-- import Formalization.NicholsZoeller  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobenius.Assembly
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobenius.PositiveMatrix
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobenius.SimplexFixedPoint
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobeniusFin1
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobeniusProof
import sympy.atlas.v1.Atlas.TensorCategories.code.PivotalSpherical
import sympy.atlas.v1.Atlas.TensorCategories.code.PointedCoalgebras
import sympy.atlas.v1.Atlas.TensorCategories.code.PointedTensorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra
-- import Formalization.ProjectiveUnitSemisimple  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_15_5
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_27_1
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_2_4
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_32_3
-- import Formalization.Proposition_1_36_4  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_36_5  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_42_9  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_43_4  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_45_2
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_45_5
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_46_2
-- import Formalization.Proposition_1_52_5  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_1_6_4
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_2_10_7
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_2_12_2
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_2_1_3
import sympy.atlas.v1.Atlas.TensorCategories.code.Proposition_2_8_7
import sympy.atlas.v1.Atlas.TensorCategories.code.QBinomial
import sympy.atlas.v1.Atlas.TensorCategories.code.QuantumGroupGeneral
-- import Formalization.QuantumGroups  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.QuantumSl2
import sympy.atlas.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
import sympy.atlas.v1.Atlas.TensorCategories.code.QuantumSl2Instance
import sympy.atlas.v1.Atlas.TensorCategories.code.QuantumTrace
-- import Formalization.QuasiBialgebra  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctor
import sympy.atlas.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective
import sympy.atlas.v1.Atlas.TensorCategories.code.ReductiveGroup
import sympy.atlas.v1.Atlas.TensorCategories.code.RegularElement
import sympy.atlas.v1.Atlas.TensorCategories.code.RegularObject
import sympy.atlas.v1.Atlas.TensorCategories.code.RigidAbelianDecomp
import sympy.atlas.v1.Atlas.TensorCategories.code.RigidMonoidalDuality
import sympy.atlas.v1.Atlas.TensorCategories.code.SchurLemma
-- import Formalization.Sec1_31_38_Props  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.SemisimpleDuals
import sympy.atlas.v1.Atlas.TensorCategories.code.SemisimpleMultitensor
import sympy.atlas.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
import sympy.atlas.v1.Atlas.TensorCategories.code.SkewPrimitive
-- import Formalization.SkewPrimitiveCategorical  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.SocleFiltration
-- import Formalization.StarAlgebra  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebraCorollaries  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebras  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.SubquotientRelation
import sympy.atlas.v1.Atlas.TensorCategories.code.SurjectiveFunctor
import sympy.atlas.v1.Atlas.TensorCategories.code.SurjectiveTensorFunctor
-- import Formalization.SweedlerConcrete  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.SweedlerHopfInstance
-- import Formalization.TaftConcrete  -- commented out: conflicts with other imports
-- import Formalization.TaftHopfDataInstance  -- commented out: conflicts with other imports
-- import Formalization.TaftHopfInstance  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.TaftWilsonComponentGrouplike
-- import Formalization.TannakaBialgebra  -- commented out: conflicts with other imports
-- import Formalization.TannakaHopfReconstruction  -- commented out: conflicts with other imports
-- import Formalization.TannakaReconstruction  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorCategoryDef
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorDualAdj
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorExact
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorHomEquivHelper
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorHomEquivNaturality
-- import Formalization.TensorImageLight  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorNondegen.DualZero
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorNondegen.EvalCoevalArg
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorNondegenInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorOverAlgebra
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorProjective.DirectSummand
import sympy.atlas.v1.Atlas.TensorCategories.code.TensorProjective.TensorSummand
-- import Formalization.Theorem_1_21_3  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_22_11  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_23_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_23_2  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_34_8  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_35_6  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_50_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_53_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_2_11_2  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.TraceNonzero
-- import Formalization.TwistEquivMonoidal  -- commented out: conflicts with other imports
-- import Formalization.Twists  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.TypeclassInstanceAudit
-- import Formalization.UnitProjective  -- commented out: conflicts with other imports
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitProjectiveSemisimple
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.EndUnitField
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.EvalCoeval
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple
import sympy.atlas.v1.Atlas.TensorCategories.code.UnitSemisimplicity
import sympy.atlas.v1.Atlas.TensorCategories.code.VecCategoricalFusionData
import sympy.atlas.v1.Atlas.TensorCategories.code.VecDualMapBridge
import sympy.atlas.v1.Atlas.TensorCategories.code.VecInstances
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal.DoubleDualIso
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal.MonoidalCoherence
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal.PivotalInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal.SphericalInstance
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotal
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotalConcrete
import sympy.atlas.v1.Atlas.TensorCategories.code.VecPivotalNaturality
import sympy.atlas.v1.Atlas.TensorCategories.code.VecSemisimple
import sympy.atlas.v1.Atlas.TensorCategories.code.VecSphericalConcrete
import sympy.atlas.v1.Atlas.TensorCategories.code.VecTensorDualCoherence
import sympy.atlas.v1.Atlas.TensorCategories.code.ZPlusModules
