/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean -/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic.Ring
/-!
# Carlitz Bernoulli identity

Formalizes the symmetric Bernoulli-number sum identity from Claudio de J.
Pita Ruiz V., “Carlitz-Type and Other Bernoulli Identities”
(`https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex`),
concept `jis_grounded_fce2b7cab59026f60915e28f__carlitz_bernoulli_sum_symm`,
grounded in source file SHA-256
`9afd712145cc635f43c1d169b86bd08516c3ace3223a0763f2538204790e4087`,
exact lines 203–233 SHA-256
`1dac4569ed610222ad9901fde13d7081d71e9072b9c4e9496fd78cfe78dac5bd`.
The identity goes back to the original L. Carlitz, Problem 795,
Mathematics Magazine 44 (1971), p. 107.
-/


namespace MetaMathlibExt

open Nat Finset

noncomputable def S (m n : ℕ) : ℚ :=
  ∑ k ∈ range (m + 1), (choose m k : ℚ) * bernoulli (n + k)

noncomputable def A (m n : ℕ) : ℚ := (-1 : ℚ) ^ m * S m n

end MetaMathlibExt
