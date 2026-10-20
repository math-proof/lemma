/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ULDMotzkinNumberOfRankR.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# (u,l,d)-Motzkin numbers of rank r

Provenance: concept `jis_sem_cc3b9e9ca9863189c52ced84`,
source `jis_source_ed70e97a9239ad812ad2e1c8`
(`schork3.tex`, lines 259-275, statement `jis_a4c8498023ac94f370aead45`).
Boundary evidence only: statement `jis_6323169e4d744a20966ea9c4`.
-/

namespace MetaMathlibExt

namespace ULDMotzkin

/-- Admissible steps of rank `r`: up-steps `U_j` with `u j` colors,
level-steps with `l` colors, down-steps `D_j` with `d j` colors.
Colors are intrinsic (`Fin (u j)`, `Fin l`, `Fin (d j)`), so a zero
count yields no steps of that color. Jump sizes use `j.val + 1`, hence
never zero. Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `admissible_steps`,
statement `jis_a4c8498023ac94f370aead45`. -/
abbrev ULDMotzkinStep (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ) : Type :=
  (Σ _j : Fin r, Fin (u _j)) ⊕ Fin l ⊕ (Σ _j : Fin r, Fin (d _j))

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

/-- Decidability of the Motzkin path predicate, by computation over the
finite prefix quantification with decidability over the integers.
Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `paths`,
statement `jis_a4c8498023ac94f370aead45`. -/
instance isMotzkinPathDecPred (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    DecidablePred (IsMotzkinPath r u l d hr n) :=
  fun p => by unfold IsMotzkinPath; infer_instance

/-- Finite type of Motzkin paths, via the decidable subtype. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
instance uldMotzkinPathFintype (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    Fintype (ULDMotzkinPath r u l d hr n) :=
  Subtype.fintype _

/-- The `(u,l,d)`-Motzkin number of rank `r` and length `n`: the finite
cardinality of the path type. Requires the source rank hypothesis
`1 ≤ r`. Concept `jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
def uldMotzkinNumber (r : ℕ) (u : Fin r → ℕ) (l : ℕ) (d : Fin r → ℕ)
    (hr : 1 ≤ r) (n : ℕ) : ℕ :=
  Fintype.card (ULDMotzkinPath r u l d hr n)

/-- Definitional cardinality equation for the Motzkin number. Concept
`jis_sem_cc3b9e9ca9863189c52ced84`, source
`jis_source_ed70e97a9239ad812ad2e1c8`, clause `number`,
statement `jis_a4c8498023ac94f370aead45`. -/
theorem uldMotzkinNumber_eq_card (r : ℕ) (u : Fin r → ℕ) (l : ℕ)
    (d : Fin r → ℕ) (hr : 1 ≤ r) (n : ℕ) :
    uldMotzkinNumber r u l d hr n =
      Fintype.card { p : Fin n → ULDMotzkinStep r u l d //
        IsMotzkinPath r u l d hr n p } :=
  rfl

end ULDMotzkin

end MetaMathlibExt
