/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/AlgebraicTopologyI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.BilinFormClassification
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.BilinFormClassification
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CohomologyKunneth
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ConeAcyclicity
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ContractibleHomology
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ConvexAcyclicity
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CrossProductExistence
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.FundamentalThm
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Lemma32_4
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.MayerVietoris
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Prop30_6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.SecondIsomorphism
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section12
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section13
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section17
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section18
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section20
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section22
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section23
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section24
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section25
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section28
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section29
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section30
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section32
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section35
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section36
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section37
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section38
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section4
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section7
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section9
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.StandardFormBridge
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.SubdivisionSmall
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Category
import Def.v1.Atlas.AlgebraicTopologyI.code.CohomologyKunneth.Part2
import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConeAcyclicity
import Def.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology.Part2
import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.DirectLimitExact
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section21
import Theorem.v1.Atlas.AlgebraicTopologyI.code.DirectLimitHomology
import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Functor
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part5
import Class.v1.Atlas.AlgebraicTopologyI.code.GradedCoalgebra
import Theorem.v1.Atlas.AlgebraicTopologyI.code.KunnethIsos
import Def.v1.Atlas.AlgebraicTopologyI.code.Lemma32_4
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris.Part4
import Structure.v1.Atlas.AlgebraicTopologyI.code.ModelChains
import Def.v1.Atlas.AlgebraicTopologyI.code.Prop30_6
import Def.v1.Atlas.AlgebraicTopologyI.code.SecondIsomorphism
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.Section12.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part3
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section14
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section18
import Def.v1.Atlas.AlgebraicTopologyI.code.Section20
import Def.v1.Atlas.AlgebraicTopologyI.code.Section22.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Section23.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Section24.Part5
import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
import Def.v1.Atlas.AlgebraicTopologyI.code.Section28
import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part7
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section32.Part2
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part14
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part14
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section38.Part3
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section4
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section7.Part3
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section9.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.StandardFormBridge
import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part3


