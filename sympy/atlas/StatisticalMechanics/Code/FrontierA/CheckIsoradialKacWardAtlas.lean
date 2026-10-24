/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/CheckIsoradialKacWardAtlas.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas

open StatMech.FrontierA.CriticalIsoradialClosedFlatSurfaceEmbedding

#print axioms
  toAdmissibleClosedFlatSurfaceEmbedding
#print axioms toOddConeGaussBonnetData
#print axioms toDualityCertificate
#print axioms surface_kacWard_arf_formula
#print axioms normalized_kacWard_duality
