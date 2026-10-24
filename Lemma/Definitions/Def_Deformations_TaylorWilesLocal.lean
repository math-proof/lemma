import Mathlib

set_option autoImplicit false

open Module

namespace TaylorWiles

variable {k : Type*} [Field k]

local notation "M₂ " k => Matrix (Fin 2) (Fin 2) k

noncomputable def adAction (M : M₂ k) : Module.End k (M₂ k) :=
  LinearMap.mulLeft k M - LinearMap.mulRight k M

@[simp] lemma adAction_apply (M X : M₂ k) : adAction M X = M * X - X * M := rfl

def disc (M : M₂ k) : k := M.trace ^ 2 - 4 * M.det

variable (k) in

noncomputable def traceZero : Submodule k (M₂ k) :=
  LinearMap.ker (Matrix.traceLinearMap (Fin 2) k k)

@[simp] lemma mem_traceZero_iff {X : M₂ k} : X ∈ traceZero k ↔ X.trace = 0 :=
  Iff.rfl

end TaylorWiles
