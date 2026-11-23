/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniVeronese.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Order
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Instance.v1.Atlas.AlgebraicGeometryI.code.BertiniVeronese

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace BertiniVeronese

/-- A property `P` holds *generically* on `α` if it holds on a dense open subset. -/
def IsGenericProperty {α : Type*} [TopologicalSpace α] (P : α → Prop) : Prop :=
  ∃ U : Set α, IsOpen U ∧ Dense U ∧ ∀ x ∈ U, P x

/-- The hypersurface `V(f) ⊂ ℙⁿ` is smooth: at every nonzero point where all partial derivatives
of `f` vanish, the value `f(x)` is nonzero (i.e. `x` is not on the hypersurface). -/
def IsSmooth_hypersurface {k : Type} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∀ x : Fin (n + 1) → k, x ≠ 0 →
    (∀ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) = 0) →
    MvPolynomial.eval x f ≠ 0

end BertiniVeronese
end
