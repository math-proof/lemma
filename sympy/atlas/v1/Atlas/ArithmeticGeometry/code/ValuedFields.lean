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

open Filter Topology

def SeqConvergesTo {k : Type*} [SeminormedAddCommGroup k] (x : ℕ → k) (ℓ : k) : Prop :=
  Filter.Tendsto x Filter.atTop (nhds ℓ)

def IsCauchySeq (x : ℕ → k) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖x m - x n‖ < ε

def SeqEquiv {k : Type*} [SeminormedAddCommGroup k] (a b : ℕ → k) : Prop :=
  Filter.Tendsto (fun n => a n - b n) Filter.atTop (nhds 0)

def IsCompleteField (k : Type*) [NormedField k] : Prop :=
  ∀ (x : ℕ → k), CauchySeq x → ∃ ℓ : k, Filter.Tendsto x Filter.atTop (nhds ℓ)


end CompleteField

abbrev NormedFieldCompletion := UniformSpace.Completion k

noncomputable instance NormedFieldCompletion.instField :
    Field (UniformSpace.Completion k) := UniformSpace.Completion.instField

noncomputable instance NormedFieldCompletion.instNormedField :
    NormedField (UniformSpace.Completion k) := inferInstance

instance NormedFieldCompletion.instCompleteSpace :
    CompleteSpace (UniformSpace.Completion k) := inferInstance

variable {k}


noncomputable def completionEmbedding (k : Type*) [NormedField k] [CompletableTopField k] :
    k →+* UniformSpace.Completion k :=
  UniformSpace.Completion.coeRingHom


end Completion

section Theorem715

variable (k : Type*) [NormedField k]

noncomputable def completion_extensionHom
    (f : k →+* k') (hf : Continuous f) :
    UniformSpace.Completion k →+* k' :=
  UniformSpace.Completion.extensionHom f hf


end Corollary717

section Corollary716

variable (k : Type*) [NormedField k]
