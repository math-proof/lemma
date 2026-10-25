/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CanonicalBrownianSLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicModulus
import Theorem.StatisticalMechanics.Code.SLE.LoewnerHolomorphicDependence.Part3
open MeasureTheory


namespace StatMech.SLE

noncomputable def canonicalBrownianLoewnerDomain (kappa : Real) :
    (Real -> Real) -> Real -> Set Complex :=
  fun omega => loewnerUnswallowedDomain
    (sleDriving kappa brownianContinuousModification omega)


noncomputable def canonicalBrownianLoewnerMaps (kappa : Real) :
    (Real -> Real) -> Real -> Complex -> Complex :=
  fun omega => loewnerMaximalMaps
    (sleDriving kappa brownianContinuousModification omega)


noncomputable def canonicalBrownianLoewnerHull (kappa : Real) :
    (Real -> Real) -> Real -> Set Complex :=
  fun omega => loewnerSwallowedSet
    (sleDriving kappa brownianContinuousModification omega)


end StatMech.SLE
