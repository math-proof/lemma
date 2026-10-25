/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Abbrev.Combinatorics.Enumerative.ULDMotzkinNumberOfRankR
/-!
# (u,l,d)-Motzkin numbers of rank r

Provenance: concept `jis_sem_cc3b9e9ca9863189c52ced84`,
source `jis_source_ed70e97a9239ad812ad2e1c8`
(`schork3.tex`, lines 259-275, statement `jis_a4c8498023ac94f370aead45`).
Boundary evidence only: statement `jis_6323169e4d744a20966ea9c4`.
-/


namespace MetaMathlibExt

namespace ULDMotzkin

/-- Height displacement of one admissible step: `+(j+1)` for an up-step,
`0` for a level-step, `-(j+1)` for a down-step. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `admissible_steps`,
statement `jis_a4c8498023ac94f370aead45`. -/
def stepHeight (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ)
    (s : ULDMotzkinStep r u l d) : ℤ :=
  match s with
  | Sum.inl ⟨j, _⟩ => ((j.val + 1 : ℕ) : ℤ)
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr ⟨j, _⟩) => -((j.val + 1 : ℕ) : ℤ)

/-- Height after the first `k` steps of a length-`n` step sequence,
summing displacements over `Finset.range k`. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
def pathHeight (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) (n : ℕ)
    (p : Fin n → ULDMotzkinStep r u l d) (k : ℕ) : ℤ :=
  Finset.sum (Finset.range k)
    (fun i => if h : i < n then stepHeight r u l d (p ⟨i, h⟩) else 0)

/-- A sequence of exactly `n` admissible steps is a Motzkin path when every
prefix height (computed from the actual steps by `pathHeight`) is
nonnegative and the final height is zero. Requires the source rank
hypothesis `1 ≤ r`. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
def IsMotzkinPath (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) (_hr : 1 ≤ r)
    (n : ℕ) (p : Fin n → ULDMotzkinStep r u l d) : Prop :=
  (∀ k ∈ Finset.range (n + 1), 0 ≤ pathHeight r u l d n p k) ∧
    pathHeight r u l d n p n = 0

/-- Type of colored Motzkin paths of rank `r` and length `n`: sequences of
exactly `n` admissible steps satisfying `IsMotzkinPath`. Requires the
source rank hypothesis `1 ≤ r`. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
def ULDMotzkinPath (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) (hr : 1 ≤ r)
    (n : ℕ) : Type :=
  { p : Fin n → ULDMotzkinStep r u l d // IsMotzkinPath r u l d hr n p }

end ULDMotzkin
end MetaMathlibExt
