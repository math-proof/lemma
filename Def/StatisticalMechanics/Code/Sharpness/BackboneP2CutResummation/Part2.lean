/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def shb_cutLeftWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (a : {e : G.edgeFinset // P e} → ℕ) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutLeft G P a))

noncomputable def shb_cutRightWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (b : {e : G.edgeFinset // ¬ P e} → ℕ) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutRight G P b))

noncomputable def shb_cutJoinWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab : ({e : G.edgeFinset // P e} → ℕ) ×
      ({e : G.edgeFinset // ¬ P e} → ℕ)) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutJoin G P ab))

end StatMech.Sharpness
