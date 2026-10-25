/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencilsAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part7
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.LefschetzPencils
set_option autoImplicit false


#check @HasComplexCoords₂


#check @HasComplexCoord₁


#check @HasHandlebodyDecomposition


#check @HasEulerCharacteristic


#check @HasAdjunctionData


#check @HasAdjunctionData.gauss_bonnet
#check @HasAdjunctionData.normal_bundle_degree
#check @HasAdjunctionData.chern_split


#check @adjunction_genus_bound_axiom


#check @HasAdjunctionData.genus_formula
#check @adjunction_formula
#check @adjunction_inequality_fiber_genus


#check @gompf_construction
#check @donaldson_lefschetz_pencil
#check @symplectic_sum_exists
#check @gompf_fundamental_group
#check @adjunction_genus_bound_axiom


#check @thurston_symplectic_fibration
#check @branched_cover_perturbation_nondegeneracy
#check @branched_cover_symplectic


