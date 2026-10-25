/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler
set_option autoImplicit false

open DifferentialFormSpace


/-- Propositional version of `HasProjectiveEmbedding`: there exists a target
differential form space, an embedding, and a closed form whose pullback represents
$[\omega]$ in de Rham cohomology. -/
def HasProjectiveEmbeddingProp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Prop :=
  ∃ (_N : ℕ) (Ω_target : ℕ → Type) (VF_target : Type)
    (inst_target : DifferentialFormSpace Ω_target VF_target)
    (emb : DFSMorphism Ω VF Ω_target VF_target)
    (targetForm : Ω_target 2),
    inst_target.d targetForm = 0 ∧
    ∃ (α : Ω 1), @DFSMorphism.pullback _ _ _ _ inst inst_target emb (p := 2) targetForm =
      S.ω + inst.d α

