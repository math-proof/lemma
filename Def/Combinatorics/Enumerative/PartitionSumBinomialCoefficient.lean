/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PartitionSumBinomialCoefficient.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

open Finset

noncomputable def wgt (m : ℕ) (k : Fin (m + 1) → ℕ) : ℕ :=
  ∑ i : Fin (m + 1), (i : ℕ) * k i

noncomputable def summand (m : ℕ) (k : Fin (m + 1) → ℕ) : ℕ :=
  Nat.multinomial Finset.univ k * ∏ i : Fin (m + 1), (m.choose (i : ℕ)) ^ k i

-- Part B: nested binomial products

noncomputable def suffixSum {m : ℕ} (s : Fin m → ℕ) (j : Fin m) : ℕ :=
  ∑ i : Fin m, if j < i then s i else 0

noncomputable def nestProd {m : ℕ} (n : ℕ) (s : Fin m → ℕ) : ℕ :=
  ∏ j : Fin m, Nat.choose (n - suffixSum s j) (s j)

-- Part C: bijection between multinomial indices and target partitions

noncomputable def tgt (m l : ℕ) : Type := Fin m → Fin (l + 1)

noncomputable def tgtPred (m l : ℕ) (s : tgt m l) : Prop :=
  ∑ k : Fin m, ((k : ℕ) + 1) * ((s k : Fin (l + 1)) : ℕ) = l

noncomputable def tgtValSum (m l : ℕ) (s : tgt m l) : ℕ :=
  ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ)

noncomputable def tgtTerm (n m l : ℕ) (s : tgt m l) : ℕ :=
  ∏ k : Fin m,
    Nat.choose (n - ∑ i : Fin m, if k < i then (((s i : Fin (l + 1))) : ℕ) else 0)
      ((((s k : Fin (l + 1))) : ℕ)) *
    Nat.choose m ((k : ℕ) + 1) ^ ((((s k : Fin (l + 1))) : ℕ))

noncomputable def fwd (m l : ℕ) (k : Fin (m + 1) → ℕ) : tgt m l :=
  fun j => ⟨min (k j.succ) l, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

noncomputable def bwd (n m l : ℕ) (s : tgt m l) : Fin (m + 1) → ℕ :=
  (Fin.cons (n - ∑ j : Fin m, (((s j : Fin (l + 1))) : ℕ))
    (fun j : Fin m => (((s j : Fin (l + 1))) : ℕ)) : Fin (m + 1) → ℕ)

end MetaMathlibExt
