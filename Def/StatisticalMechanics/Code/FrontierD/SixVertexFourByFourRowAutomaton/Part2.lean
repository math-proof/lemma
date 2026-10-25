/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByFourRowAutomaton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourTwoCycleMatching.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByFourRowAutomaton


namespace StatMech.FrontierD

def sixVertexFourByFourAuditedFirstStateDecode (row : SixVertexRow 4) : Option (Fin 4) :=
  let code := Nat.ofBits row
  if code = 1 then some 0
  else if code = 2 then some 1
  else if code = 4 then some 2
  else if code = 8 then some 3
  else none

def sixVertexFourByFourAuditedSecondStateDecode (row : SixVertexRow 4) : Option (Fin 4) :=
  let code := Nat.ofBits row
  if code = 7 then some 0
  else if code = 11 then some 1
  else if code = 13 then some 2
  else if code = 14 then some 3
  else none

end StatMech.FrontierD
