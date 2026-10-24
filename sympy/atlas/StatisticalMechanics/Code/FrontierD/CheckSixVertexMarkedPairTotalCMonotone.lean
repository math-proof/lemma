/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/CheckSixVertexMarkedPairTotalCMonotone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairTotalCMonotone

open StatMech.FrontierD

#print axioms markedDecorationMultiplicity_mono
#print axioms sixVertexMarkedPairMultiplicityNat_mono_of_totalC
#print axioms markedDecoratedPairEmbeddingOfTotalCLe
#print axioms sixVertexMarkedSectorPairMass_le_of_totalCEmbedding
#print axioms sixVertexMarkedTraceCoefficientwiseLogConcave_of_totalCEmbedding
