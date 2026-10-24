/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteDenseAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.KFiniteProps
import Lemma.Complex.inner.of.IsUnitary
import Lemma.Set.Dense_KFiniteSubspace.of.IsAdmissible
import Lemma.Complex.ConvolutionOp.eq.Integral_MulConvolutionKernel
import sympy.atlas.v1.Atlas.LieGroups.code.HarishChandraFunctor
import sympy.atlas.v1.Atlas.LieGroups.code.PlancherelCompact


section Verification

open ContinuousRep


#check @kFiniteSubspace_dense

#check @measureRep_exists


#check @PlancherelCompact.kfinite_dense_in_rep
#check @PlancherelCompact.leftRegularRep_CK
#check @PlancherelCompact.isKFinite_leftReg_implies_isKFiniteFunction
#check @PlancherelCompact.kfinite_functions_uniformly_dense
#check @PlancherelCompact.kfinite_dense_in_continuous
#check @PlancherelCompact.kfinite_ck_dense
#check @PlancherelCompact.kfinite_functions_smooth_dense

end Verification
