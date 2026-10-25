/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4ParameterBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9


namespace StatMech.FrontierD

noncomputable def fkQgt4SixVertexWeight (q : ℝ) : ℝ :=
  Real.sqrt (2 + Real.sqrt q)

end StatMech.FrontierD
