/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuedFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.UniformField
import Instance.v1.Atlas.ArithmeticGeometry.code.ValuedFields
open Filter Topology

variable {k}


noncomputable def completionEmbedding (k : Type*) [NormedField k] [CompletableTopField k] :
    k →+* UniformSpace.Completion k :=
  UniformSpace.Completion.coeRingHom


section Theorem715

variable (k : Type*) [NormedField k]

noncomputable def completion_extensionHom
    (f : k →+* k') (hf : Continuous f) :
    UniformSpace.Completion k →+* k' :=
  UniformSpace.Completion.extensionHom f hf


end Theorem715
