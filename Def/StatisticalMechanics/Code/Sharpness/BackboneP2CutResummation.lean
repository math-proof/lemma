/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CutResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def shb_cutEquiv (P : G.edgeFinset → Prop) [DecidablePred P] :
    (G.edgeFinset → ℕ) ≃
      ({e : G.edgeFinset // P e} → ℕ) ×
        ({e : G.edgeFinset // ¬ P e} → ℕ) :=
  Equiv.piEquivPiSubtypeProd P (fun _ => ℕ)


noncomputable def shb_cutLeft (P : G.edgeFinset → Prop) [DecidablePred P]
    (a : {e : G.edgeFinset // P e} → ℕ) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm (a, fun _ => 0)


noncomputable def shb_cutRight (P : G.edgeFinset → Prop) [DecidablePred P]
    (b : {e : G.edgeFinset // ¬ P e} → ℕ) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm (fun _ => 0, b)


noncomputable def shb_cutJoin (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab : ({e : G.edgeFinset // P e} → ℕ) ×
      ({e : G.edgeFinset // ¬ P e} → ℕ)) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm ab

end StatMech.Sharpness
