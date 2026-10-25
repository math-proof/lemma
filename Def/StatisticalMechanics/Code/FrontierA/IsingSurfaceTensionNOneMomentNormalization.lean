/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneExponentBounds
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneMomentNormalization
open Finset


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

noncomputable def normalizedTermWeight (X : Real) (t : BiTerm) : Real :=
  (t.coeff : Real) * X ^ t.ex

noncomputable def normalizedTermInteraction (t : BiTerm) : Real :=
  (2 * t.ey - 9 : Int)

end StatMech.FrontierA.NOneSymmetricMeanCertificate
