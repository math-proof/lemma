/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckIsingSpinAffineSimilarityTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSpinAffineSimilarityTransport

open StatMech.FrontierA

#print axioms
  squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel
#print axioms
  tendsto_squareBoxRenormalizedSpinCorrelation_uniformScale_of_reindexed_relabel
#print axioms deriv_inverseUniformScaleAffineConformalMap
#print axioms spinConformalFactor_inverseUniformScaleAffineConformalMap
#print axioms
  tendsto_squareBoxRenormalizedSpinCorrelation_affine_of_reindexed_relabel
#print axioms
  tendsto_squareBoxRenormalizedSpinCorrelation_affine_reindex
