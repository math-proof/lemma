/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalAptSystemVerification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineSLVStrong
import Lemma.Set.IsOpen_SLVSet_SLV.of.IsOpen_SetOfIsInMaxIdeal.IsOpen_SetOfIsInO.All_Continuous.EqSet_SLVIwahoriSetSLV.IsAdicComplete_MaxIdeal


#check @AffineBuildingSLVStrong.slv_strongly_transitive_maximal_apartment_system
#check @AffineBuildingSLVStrong.constructed_apartment_system_is_maximal
#check @AffineBuildingSLVStrong.iwahori_maximal_apartment_chain
#check @AffineBuildingSLVStrong.slv_maximal_apartment_system
#check @AffineBuildingSLVStrong.frame_apartment_system_stable
#check @AffineBuildingSLVStrong.maximal_apt_system_slv_helper
#check @AffineBuildingSLVStrong.constructed_apartment_system_is_maximal_of_stable_and_transitive
#check @AffineBuildingSLVStrong.strong_transitivity_from_compact_open_iwahori
