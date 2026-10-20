import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.VaughanIdentity
open scoped BigOperators
open MetaMathlibExt


/--
[vaughan_identity_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/VaughanIdentity.lean)
-/
@[path]
private lemma vaughan_identity_general_eq
  [CommRing R]
  {μ Λ : ArithmeticFunction R}
  {logW : ℕ → R}
  {U V n : ℕ}
-- given
  (hn : V < n)
  (hLambda : ∀ m, Λ m = ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d * logW (m / d))
  (hMu : ∀ m, ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d = if m = 1 then 1 else 0) :
-- imply
  Λ n = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
    μ b * logW (n / b))
    - (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
    ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
    μ b * Λ c)
    + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
    ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
    μ b * Λ c) := by
-- proof
  apply MetaMathlibExt.vaughan_identity_general μ Λ logW U V n hn hLambda hMu

/--
[vaughan_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/VaughanIdentity.lean)
-/
@[path]
private lemma vaughan_identity_eq
  [CommRing R]
  {μ Λ : ArithmeticFunction R}
  {logW : ℕ → R}
  {U V n : ℕ}
-- given
  (hU : 1 ≤ U)
  (hV : 1 ≤ V)
  (hn : V < n)
  (hLambda : ∀ m, Λ m = ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d * logW (m / d))
  (hMu : ∀ m, ∑ d ∈ (Finset.range (m + 1)).filter (fun d => d ∣ m), μ d = if m = 1 then 1 else 0) :
-- imply
  Λ n = (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
    μ b * logW (n / b))
    - (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ b ≤ U),
    ∑ c ∈ (Finset.range (n + 1)).filter (fun c => c ≤ V ∧ b * c ∣ n),
    μ b * Λ c)
    + (∑ b ∈ (Finset.range (n + 1)).filter (fun b => b ∣ n ∧ U < b),
    ∑ c ∈ (Finset.range (n + 1)).filter (fun c => V < c ∧ b * c ∣ n),
    μ b * Λ c) := by
-- proof
  apply MetaMathlibExt.vaughan_identity μ Λ logW U V n hU hV hn hLambda hMu


-- created on 2026-10-20
