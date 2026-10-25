/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/TensorCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.AlgebraInCategory
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategories.Part4
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
import Def.v1.Atlas.TensorCategories.code.AlgebrasInCategoriesDefs.Part3
import Abbrev.v1.Atlas.TensorCategories.code.BasicMonoidalDefs.Part5
import Theorem.v1.Atlas.TensorCategories.code.BialgebraReconstruction
import Abbrev.v1.Atlas.TensorCategories.code.Bimodule
import Theorem.v1.Atlas.TensorCategories.code.BuildStubAudit
import Theorem.v1.Atlas.TensorCategories.code.BuildVerified
import Theorem.v1.Atlas.TensorCategories.code.CategoricalDimension
import Def.v1.Atlas.TensorCategories.code.Ch1Theorems
import Structure.v1.Atlas.TensorCategories.code.ChevalleyProperty.Part2
import Abbrev.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part4
import Def.v1.Atlas.TensorCategories.code.ComoduleDuals
import Theorem.v1.Atlas.TensorCategories.code.ConcreteInstancesModule
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
import Def.v1.Atlas.TensorCategories.code.Corollary_1_13_4
import Class.v1.Atlas.TensorCategories.code.Corollary_1_13_7
import Theorem.v1.Atlas.TensorCategories.code.Corollary_1_15_2
import Theorem.v1.Atlas.TensorCategories.code.Corollary_1_15_9
import Instance.v1.Atlas.TensorCategories.code.Corollary_1_22_6
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
import Theorem.v1.Atlas.TensorCategories.code.Corollary_1_31_5
import Def.v1.Atlas.TensorCategories.code.Corollary_1_48_3
import Instance.v1.Atlas.TensorCategories.code.Definition_1_15_4
import Def.v1.Atlas.TensorCategories.code.Definition_1_18_1
import Abbrev.v1.Atlas.TensorCategories.code.Definition_1_18_2
import Abbrev.v1.Atlas.TensorCategories.code.Definition_1_34_1
import Abbrev.v1.Atlas.TensorCategories.code.Definition_1_45_7
import Abbrev.v1.Atlas.TensorCategories.code.Definition_1_46_1
import Def.v1.Atlas.TensorCategories.code.Definition_2_1_6
import Abbrev.v1.Atlas.TensorCategories.code.Definition_2_3_1
import Theorem.v1.Atlas.TensorCategories.code.Definition_2_9_1
import Def.v1.Atlas.TensorCategories.code.Definition_2_9_18_ExactAlgebra
import Def.v1.Atlas.TensorCategories.code.DeligneTensorProduct.Part3
import Structure.v1.Atlas.TensorCategories.code.DeligneTensorProductDef
import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import Def.v1.Atlas.TensorCategories.code.DirectSumModuleCategory.Part2
import Structure.v1.Atlas.TensorCategories.code.DirectSumModuleCategoryDef
import Instance.v1.Atlas.TensorCategories.code.DualCategory.Part6
import Theorem.v1.Atlas.TensorCategories.code.DualCoherenceBridge
import Abbrev.v1.Atlas.TensorCategories.code.DualDefinitions
import Instance.v1.Atlas.TensorCategories.code.EndTensorProduct
import Def.v1.Atlas.TensorCategories.code.ExactModuleCatEquiv.Part3
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Abbrev.v1.Atlas.TensorCategories.code.ExactModuleCriteria.Part2
import Class.v1.Atlas.TensorCategories.code.Ext1UnitVanishing.Part2
import Def.v1.Atlas.TensorCategories.code.FPdimCategory
import Theorem.v1.Atlas.TensorCategories.code.FPdimCosine
import Theorem.v1.Atlas.TensorCategories.code.FPdimFunctor
import Def.v1.Atlas.TensorCategories.code.FPdimProps.Part3
import Def.v1.Atlas.TensorCategories.code.FiberFunctor
import Def.v1.Atlas.TensorCategories.code.FiberFunctorEnd
import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Theorem.v1.Atlas.TensorCategories.code.FiniteCategoryDef
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Theorem.v1.Atlas.TensorCategories.code.FittingAlgebraLocalRing
import Instance.v1.Atlas.TensorCategories.code.FittingLemmaInstance
import Class.v1.Atlas.TensorCategories.code.FittingLemmaLocalEnd
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Instance.v1.Atlas.TensorCategories.code.GrothendieckFusionRingInstance.Part2
import Def.v1.Atlas.TensorCategories.code.GrothendieckModuleIrreducible
import Theorem.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Def.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part5
import Instance.v1.Atlas.TensorCategories.code.HigherDerivation
import Def.v1.Atlas.TensorCategories.code.HomExactImpliesExact.Part2
import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraAntiHom
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebraRep.Part2
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Instance.v1.Atlas.TensorCategories.code.Instances.VecFiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.IntegralCategories
import Def.v1.Atlas.TensorCategories.code.IntegralsClean
import Def.v1.Atlas.TensorCategories.code.InternalHom.Part4
import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
import Instance.v1.Atlas.TensorCategories.code.K0Bimodule.Part5
import Def.v1.Atlas.TensorCategories.code.Lemma285
import Def.v1.Atlas.TensorCategories.code.Lemma_1_30_2
import Class.v1.Atlas.TensorCategories.code.Lemma_1_51_1.Part2
import Structure.v1.Atlas.TensorCategories.code.Lemma_2_14_7
import Def.v1.Atlas.TensorCategories.code.LocalEndRingsInstance
import Abbrev.v1.Atlas.TensorCategories.code.LocallyFiniteDefs
import Theorem.v1.Atlas.TensorCategories.code.MacLaneCoherence
import Instance.v1.Atlas.TensorCategories.code.MacLaneStrictness.Part2
import Structure.v1.Atlas.TensorCategories.code.ModuleCategory.Theorem2112
import Class.v1.Atlas.TensorCategories.code.ModuleCategory.Theorem2116
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ModuleCategoryDecomp
import Structure.v1.Atlas.TensorCategories.code.ModuleCategoryEquiv
import Theorem.v1.Atlas.TensorCategories.code.ModuleCategoryMultitensor
import Structure.v1.Atlas.TensorCategories.code.ModuleFunctor
import Class.v1.Atlas.TensorCategories.code.ModuleFunctorAbelianDefs
import Theorem.v1.Atlas.TensorCategories.code.ModuleFunctorCategory
import Def.v1.Atlas.TensorCategories.code.ModuleFunctorCategoryAbelianInstance
import Class.v1.Atlas.TensorCategories.code.ModuleFunctorDefs
import Theorem.v1.Atlas.TensorCategories.code.ModuleFunctorFinite
import Abbrev.v1.Atlas.TensorCategories.code.ModuleOverAlgebra.Part2
import Instance.v1.Atlas.TensorCategories.code.ModuleRigidityCompat
import Abbrev.v1.Atlas.TensorCategories.code.MonoidalFunctorDef
import Instance.v1.Atlas.TensorCategories.code.MonoidalFunctorProps.Part2
import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorsCohomology.Part5
import Def.v1.Atlas.TensorCategories.code.MonoidalStructuresGraded
import Def.v1.Atlas.TensorCategories.code.MoritaEquivalence
import Theorem.v1.Atlas.TensorCategories.code.PerronFrobenius.Assembly
import Theorem.v1.Atlas.TensorCategories.code.PerronFrobenius.PositiveMatrix
import Def.v1.Atlas.TensorCategories.code.PerronFrobenius.SimplexFixedPoint
import Theorem.v1.Atlas.TensorCategories.code.PerronFrobeniusFin1
import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Theorem.v1.Atlas.TensorCategories.code.PointedCoalgebras
import Abbrev.v1.Atlas.TensorCategories.code.PointedTensorCategory
import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part4
import Def.v1.Atlas.TensorCategories.code.Proposition_1_15_5
import Instance.v1.Atlas.TensorCategories.code.Proposition_1_27_1.Part2
import Def.v1.Atlas.TensorCategories.code.Proposition_1_2_4
import Theorem.v1.Atlas.TensorCategories.code.Proposition_1_32_3
import Def.v1.Atlas.TensorCategories.code.Proposition_1_45_2
import Abbrev.v1.Atlas.TensorCategories.code.Proposition_1_45_5
import Theorem.v1.Atlas.TensorCategories.code.Proposition_1_46_2
import Abbrev.v1.Atlas.TensorCategories.code.Proposition_1_6_4
import Def.v1.Atlas.TensorCategories.code.Proposition_2_10_7
import Instance.v1.Atlas.TensorCategories.code.Proposition_2_12_2
import Def.v1.Atlas.TensorCategories.code.Proposition_2_1_3
import Theorem.v1.Atlas.TensorCategories.code.Proposition_2_8_7
import Theorem.v1.Atlas.TensorCategories.code.QBinomial.Part2
import Class.v1.Atlas.TensorCategories.code.QuantumGroupGeneral
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part5
import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Instance
import Theorem.v1.Atlas.TensorCategories.code.QuantumTrace
import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Class.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective.Part3
import Structure.v1.Atlas.TensorCategories.code.ReductiveGroup
import Structure.v1.Atlas.TensorCategories.code.RegularElement
import Abbrev.v1.Atlas.TensorCategories.code.RegularObject.Part2
import Def.v1.Atlas.TensorCategories.code.RigidAbelianDecomp.Part2
import Def.v1.Atlas.TensorCategories.code.RigidMonoidalDuality.Part2
import Theorem.v1.Atlas.TensorCategories.code.SchurLemma
import Theorem.v1.Atlas.TensorCategories.code.SemisimpleDuals
import Def.v1.Atlas.TensorCategories.code.SemisimpleMultitensor.Part6
import Theorem.v1.Atlas.TensorCategories.code.SimpleObjectHelpers
import Abbrev.v1.Atlas.TensorCategories.code.SkewPrimitive
import Def.v1.Atlas.TensorCategories.code.SocleFiltration
import Def.v1.Atlas.TensorCategories.code.SubquotientRelation
import Class.v1.Atlas.TensorCategories.code.SurjectiveFunctor
import Class.v1.Atlas.TensorCategories.code.SurjectiveTensorFunctor
import Instance.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part4
import Theorem.v1.Atlas.TensorCategories.code.TaftWilsonComponentGrouplike
import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
import Def.v1.Atlas.TensorCategories.code.TensorDualAdj
import Def.v1.Atlas.TensorCategories.code.TensorExact.Part3
import Theorem.v1.Atlas.TensorCategories.code.TensorHomEquivHelper
import Theorem.v1.Atlas.TensorCategories.code.TensorHomEquivNaturality
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.DualZero
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.EvalCoevalArg
import Def.v1.Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
import Instance.v1.Atlas.TensorCategories.code.TensorNondegenInstance
import Theorem.v1.Atlas.TensorCategories.code.TensorOverAlgebra
import Theorem.v1.Atlas.TensorCategories.code.TensorProjective.DirectSummand
import Def.v1.Atlas.TensorCategories.code.TensorProjective.TensorSummand
import Def.v1.Atlas.TensorCategories.code.TraceNonzero
import Theorem.v1.Atlas.TensorCategories.code.TypeclassInstanceAudit
import Class.v1.Atlas.TensorCategories.code.UnitProjectiveSemisimple
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.EndUnitField
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.EvalCoeval
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.MonoidalBiexact.Part4
import Instance.v1.Atlas.TensorCategories.code.UnitSemisimplicity.TensorExactness
import Structure.v1.Atlas.TensorCategories.code.UnitSemisimplicity.UnitSimple
import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity
import Instance.v1.Atlas.TensorCategories.code.VecCategoricalFusionData
import Theorem.v1.Atlas.TensorCategories.code.VecDualMapBridge
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Def.v1.Atlas.TensorCategories.code.VecPivotal.DoubleDualIso
import Def.v1.Atlas.TensorCategories.code.VecPivotal.MonoidalCoherence
import Theorem.v1.Atlas.TensorCategories.code.VecPivotal.PivotalInstance
import Theorem.v1.Atlas.TensorCategories.code.VecPivotal.SphericalInstance
import Instance.v1.Atlas.TensorCategories.code.VecPivotal
import Def.v1.Atlas.TensorCategories.code.VecPivotalConcrete.Part2
import Theorem.v1.Atlas.TensorCategories.code.VecPivotalNaturality
import Instance.v1.Atlas.TensorCategories.code.VecSemisimple.Part2
import Theorem.v1.Atlas.TensorCategories.code.VecSphericalConcrete
import Def.v1.Atlas.TensorCategories.code.VecTensorDualCoherence
import Structure.v1.Atlas.TensorCategories.code.ZPlusModules.Part6
-- import Formalization.AlgebrasInCategoriesDefsBatch  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.Assembly  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.Injective  -- commented out: conflicts with other imports
-- import Formalization.AntipodeBijective.RankEquality  -- commented out: conflicts with other imports
-- import Formalization.BasedRings  -- commented out: conflicts with other imports
-- import Formalization.BasedRingsGeneral  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.Axioms  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.CommHopfFunGroup  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant.Theorems  -- commented out: conflicts with other imports
-- import Formalization.CartierKostant  -- commented out: conflicts with other imports
-- import Formalization.CategoricalFreeness  -- commented out: conflicts with other imports
-- import Formalization.ChevalleyTheorem -- commented out: Mathlib API change (IsSemisimpleModule.jacobson_eq_bot)
-- import Formalization.CocommutativeMonoidAlgebra  -- commented out: conflicts with other imports
-- import Formalization.ConcreteInstances  -- commented out: conflicts with other imports
-- import Formalization.ConcreteModuleCategories  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_29_7  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_43_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_43_6  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_50_3  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_50_4  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_51_3  -- commented out: conflicts with other imports
-- import Formalization.Corollary_1_51_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_2_10_5  -- commented out: conflicts with other imports
-- import Formalization.Corollary_2_14_9  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_22_2  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_52_1  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_52_6  -- commented out: conflicts with other imports
-- import Formalization.Definition_1_5_1  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_5_4  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_21  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_22  -- commented out: conflicts with other imports
-- import Formalization.Definition_2_9_24  -- commented out: conflicts with other imports
-- import Formalization.DistinguishedInvertible  -- commented out: conflicts with other imports
-- import Formalization.DrinfeldCenter  -- commented out: conflicts with other imports
-- import Formalization.DualCatDefs  -- commented out: conflicts with other imports
-- import Formalization.ExactAlgebra  -- commented out: conflicts with other imports
-- import Formalization.HopfAlgebraRigid  -- commented out: conflicts with other imports
-- import Formalization.IntegralsCartanMatrix  -- commented out: conflicts with other imports
-- import Formalization.IntegralsDefs  -- commented out: conflicts with other imports
-- import Formalization.IntegralsProps  -- commented out: conflicts with other imports
-- import Formalization.InternalHomEssSurjInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFaithfulInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFullInstance  -- commented out: conflicts with other imports
-- import Formalization.InternalHomFunctor  -- commented out: conflicts with other imports
-- import Formalization.Lemma_1_33_2  -- commented out: conflicts with other imports
-- import Formalization.Lemma_2_14_10  -- commented out: conflicts with other imports
-- import Formalization.Lemma_2_9_12  -- commented out: conflicts with other imports
-- import Formalization.MfStarAlgebra  -- commented out: conflicts with other imports
-- import Formalization.MonoidalCategoryDef  -- commented out: conflicts with other imports
-- import Formalization.MonoidalUnitProperties  -- commented out: conflicts with other imports
-- import Formalization.MultifusionSemisimple  -- commented out: conflicts with other imports
-- import Formalization.NicholsZoeller  -- commented out: conflicts with other imports
-- import Formalization.ProjectiveUnitSemisimple  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_36_4  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_36_5  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_42_9  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_43_4  -- commented out: conflicts with other imports
-- import Formalization.Proposition_1_52_5  -- commented out: conflicts with other imports
-- import Formalization.QuantumGroups  -- commented out: conflicts with other imports
-- import Formalization.QuasiBialgebra  -- commented out: conflicts with other imports
-- import Formalization.Sec1_31_38_Props  -- commented out: conflicts with other imports
-- import Formalization.SkewPrimitiveCategorical  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebra  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebraCorollaries  -- commented out: conflicts with other imports
-- import Formalization.StarAlgebras  -- commented out: conflicts with other imports
-- import Formalization.SweedlerConcrete  -- commented out: conflicts with other imports
-- import Formalization.TaftConcrete  -- commented out: conflicts with other imports
-- import Formalization.TaftHopfDataInstance  -- commented out: conflicts with other imports
-- import Formalization.TaftHopfInstance  -- commented out: conflicts with other imports
-- import Formalization.TannakaBialgebra  -- commented out: conflicts with other imports
-- import Formalization.TannakaHopfReconstruction  -- commented out: conflicts with other imports
-- import Formalization.TannakaReconstruction  -- commented out: conflicts with other imports
-- import Formalization.TensorImageLight  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_21_3  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_22_11  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_23_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_23_2  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_34_8  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_35_6  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_50_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_1_53_1  -- commented out: conflicts with other imports
-- import Formalization.Theorem_2_11_2  -- commented out: conflicts with other imports
-- import Formalization.TwistEquivMonoidal  -- commented out: conflicts with other imports
-- import Formalization.Twists  -- commented out: conflicts with other imports
-- import Formalization.UnitProjective  -- commented out: conflicts with other imports


