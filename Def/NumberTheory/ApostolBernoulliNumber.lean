/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ApostolBernoulliNumber.lean -/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
/-!
# Apostol-Bernoulli numbers
-/


namespace MetaMathlibExt

/-- Apostol-Bernoulli numbers `βₖ(α)` (concept `jis_sem_b4b0e1e624b9b6eac0d29207`,
source statement `jis_5ab17288071712819e845b9a`, equation `eq21111`): for `α ∈ ℂ`
with `α ≠ 0, 1`, the sequence `β(α)` is characterized by the exponential generating
function `t / (α * e ^ t - 1) = ∑ βₖ(α) * t ^ k / k!` for `|t| < |log α|`.
Here `Complex.log` is the principal-branch complex logarithm, so
`‖Complex.log α‖` renders the source's `|log α|`. -/
def IsApostolBernoulliSequence (α : ℂ) (β : ℕ → ℂ) : Prop :=
  α ≠ 0 ∧ α ≠ 1 ∧
    ∀ t : ℂ, ‖t‖ < ‖Complex.log α‖ →
      HasSum (fun k : ℕ => β k * t ^ k / (Nat.factorial k : ℂ))
        (t / (α * Complex.exp t - 1))

end MetaMathlibExt
