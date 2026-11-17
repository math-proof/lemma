/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HyperfactorialPartition.lean -/

module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

/-! Provenance: concept `jis_sem_c632991dc77d0efec89f490f`,
source statement `jis_2803b664db749f0c99721a41`. -/


namespace MetaMathlibExt

/-- A finite hyperfactorial digit vector is normalized when its final digit is nonzero.
The empty vector is normalized vacuously and is the canonical representation of zero. -/
def HyperfactorialDigitsNormalized (k : ℕ) (digits : Fin k → ℕ) : Prop :=
  ∀ h : 0 < k, digits ⟨k - 1, Nat.sub_lt h (by decide)⟩ ≠ 0

end MetaMathlibExt
