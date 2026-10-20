/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FormalSequence.lean -/

import Mathlib.Algebra.Field.Basic

namespace MetaMathlibExt

/-- Coefficient `α` of the formal-sequence recurrence determined by a seed
triplet `(a, b, c)`, namely `α = (ab + bc + ca) / b² - 1`.

This is from statement `jis_50a05fd3a5b6b4a1865a61bb`, concept
`jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`. -/
def formalAlpha {F : Type*} [Field F] (a b c : F) : F :=
  (a * b + b * c + c * a) / b ^ 2 - 1

/-- Constant term `β` of the formal-sequence recurrence determined by a seed
triplet `(a, b, c)`, namely `β = (b² - ac) / b`.

This is from statement `jis_50a05fd3a5b6b4a1865a61bb`, concept
`jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`. -/
def formalBeta {F : Type*} [Field F] (a b c : F) : F :=
  (b ^ 2 - a * c) / b

/-- A formal sequence extended from a seed triplet `(a, b, c)`.

The middle seed is nonzero, the first three terms are `a`, `b`, and `c`, and
the sequence satisfies `u (n + 2) = α * u (n + 1) - u n + β` for every `n`.
This is statement `jis_50a05fd3a5b6b4a1865a61bb`, concept
`jis_sem_1ce947826a0dceb6fde5b7f2`, in
<https://cs.uwaterloo.ca/journals/JIS/VOL23/Kocik/kocik5.tex>, lines 482–499.
Source SHA-256: `f216e1e1606af32792c37505ee832c53db0244b0c93f934f34619996b1aa1746`;
raw block SHA-256: `9665499a711e4ccc50f15a8b66c8cc5e643123774d2a19478a2e7605e8d72a4d`. -/
def IsFormalSequence {F : Type*} [Field F]
    (u : ℕ → F) (a b c : F) : Prop :=
  b ≠ 0 ∧ u 0 = a ∧ u 1 = b ∧ u 2 = c ∧
    ∀ n : ℕ, u (n + 2) =
      formalAlpha a b c * u (n + 1) - u n + formalBeta a b c

end MetaMathlibExt
