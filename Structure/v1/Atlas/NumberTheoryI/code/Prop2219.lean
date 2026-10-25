/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop2219.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.NumberTheoryI.code.Ch22WeberLFunction
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22WeberLFunction
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AnalyticClassNumber
import Instance.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part3
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor1838
import Def.v1.Atlas.NumberTheoryI.code.Prop2219


noncomputable section

open scoped NumberField

open Complex Finset Section19

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

structure WeberLFunction_MeromorphicExtension
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) where
  toFun : ℂ → ℂ
  eq_on_convergence : ∀ s : ℂ, 1 < s.re →
    toFun s = WeberLFunction K 𝔪 χ s
  meromorphicOn : MeromorphicOn toFun (halfPlane K)
  simple_pole_at_one : ∃ v : ℂ,
    AnalyticAt ℂ (Function.update (fun s => (s - 1) * toFun s) 1 v) 1

  holomorphic_at_one_of_nonprincipal : ¬χ.IsPrincipal → AnalyticAt ℂ toFun 1

end RayClassField
end
