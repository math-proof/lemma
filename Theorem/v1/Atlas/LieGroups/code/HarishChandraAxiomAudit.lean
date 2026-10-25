/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraAxiomAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective


noncomputable section AuditChecks

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

example := @uea_algHom_separates

example := @pbw_hc_eval_kernel_vanishing

example := @verma_embedding_scalar_invariance

example := @filtered_graded_principle_for_hc

example := @HarishChandraIso

example := @evalWeight_separates

end AuditChecks
