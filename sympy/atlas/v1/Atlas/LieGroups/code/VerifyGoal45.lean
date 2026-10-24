/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VerifyGoal45.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.VermaModules
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace


#check @IsVermaModule
#check @VermaModule
#check @vermaIdeal
#check @VermaModule.highestWeightVec
#check @verma_module_exists


#check @VermaModule.instRing
#check @VermaModule.instAddCommGroup


#check @IsVermaModule.free_over_nminus
#check @IsVermaModule.exists_unique_maximal_submodule
#check @IsVermaModule.quotient_by_maximal_irreducible
#check @IsVermaModule.highestWeightSpace_one_dim
#check @IsVermaModule.weight_set_eq
#check @IsVermaModule.highest_weight_module_is_quotient
#check @irreducible_highest_weight_unique_up_to_iso


#check @WeightSpace
#check @TriangularDecomposition.weightSubspace
#check @weightSpace_eq_mathlib_weightSpace
