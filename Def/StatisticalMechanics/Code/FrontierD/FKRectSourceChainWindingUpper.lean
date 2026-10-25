/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def connectionPathPairs {V : Type*} [DecidableEq V] (n : Nat)
    (v : Fin (n + 1) -> V) : Finset (V × V) :=
  Finset.univ.image fun i : Fin n => (v i.castSucc, v i.succ)

end
end StatMech.FrontierD
