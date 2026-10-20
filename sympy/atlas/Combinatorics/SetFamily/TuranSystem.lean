/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SetFamily/TuranSystem.lean -/

import Mathlib.Data.Fintype.Basic
import sympy.atlas.Combinatorics.SetFamily.UniformHypergraph
/-!
Turan systems after Liu and Pikhurko,
"A note on the minimum size of Turán systems" (arXiv:2501.15457v2).
Tracks source lines 138-139, 148, and 150-152 for the covering definition.
-/
namespace TuranSystem
/-- `IsTuranSystem n s r H` means `H` is `r`-uniform and every `s`-set
contains an edge of `H`, with `0 < r ∧ r < s ∧ s ≤ n`. -/
def IsTuranSystem (n s r : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  0 < r ∧ r < s ∧ s ≤ n ∧ SetFamily.IsUniform H r ∧
    ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)), ∃ e ∈ H, e ⊆ T
/-- Positivity projection from a Turan system. -/
theorem pos_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : 0 < r := h.1
/-- Strict-inequality projection from a Turan system. -/
theorem lt_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : r < s := h.2.1
/-- Size-bound projection from a Turan system. -/
theorem le_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : s ≤ n := h.2.2.1
/-- Uniformity projection from a Turan system. -/
theorem uniform_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) : SetFamily.IsUniform H r := h.2.2.2.1
/-- Covering projection: every `s`-set contains an edge of `H`. -/
theorem cover_of_isTuran (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (h : IsTuranSystem n s r H) :
    ∀ T ∈ Finset.powersetCard s (Finset.univ : Finset (Fin n)),
      ∃ e ∈ H, e ⊆ T := h.2.2.2.2
/-- The complete `r`-graph: all `r`-subsets of `Fin n`. -/
def completeGraph (n r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.powersetCard r (Finset.univ : Finset (Fin n))
/-- The complete `r`-graph is `r`-uniform. -/
theorem completeGraph_uniform (n r : ℕ) :
    SetFamily.IsUniform (completeGraph n r) r := by
  intro e he
  exact (Finset.mem_powersetCard.mp he).2
/-- The complete `r`-graph is a Turan system under the parameter bounds. -/
theorem completeGraph_isTuran (n s r : ℕ)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    IsTuranSystem n s r (completeGraph n r) := by
  refine ⟨hd.1, hd.2.1, hd.2.2, completeGraph_uniform n r, ?_⟩
  intro T hT
  have hTs : T.card = s := (Finset.mem_powersetCard.mp hT).2
  have hle : r ≤ T.card := by rw [hTs]; exact Nat.le_of_lt hd.2.1
  obtain ⟨S, hST, hSc⟩ := Finset.exists_subset_card_eq hle
  exact ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hSc⟩, hST⟩
/-- Realized sizes: cardinalities of Turan systems with parameters `n s r`. -/
def realizedCounts (n s r : ℕ) : Set ℕ :=
  { k | ∃ H, IsTuranSystem n s r H ∧ H.card = k }
/-- Membership unfolding for `realizedCounts`. -/
theorem mem_realizedCounts (n s r k : ℕ) :
    k ∈ realizedCounts n s r ↔ ∃ H, IsTuranSystem n s r H ∧ H.card = k :=
  Iff.rfl
/-- Existence of a Turan system under the parameter bounds. -/
theorem exists_system (n s r : ℕ) (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    ∃ H, IsTuranSystem n s r H :=
  ⟨_, completeGraph_isTuran n s r hd⟩
/-- The set of realized sizes is nonempty under the parameter bounds. -/
theorem realizedCounts_nonempty (n s r : ℕ)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) : ∃ k, k ∈ realizedCounts n s r :=
  ⟨_, _, completeGraph_isTuran n s r hd, rfl⟩
/-- The Turan number: least realized size, `0` when no system exists. -/
noncomputable def turanNumber (n s r : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, k ∈ realizedCounts n s r then Nat.find h else 0
/-- The Turan number is realized under the parameter bounds. -/
theorem turanNumber_mem (n s r : ℕ) (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    turanNumber n s r ∈ realizedCounts n s r := by
  classical
  have hex : ∃ k, k ∈ realizedCounts n s r := realizedCounts_nonempty n s r hd
  rw [turanNumber, dite_eq_left hex]
  exact Nat.find_spec hex
/-- Attainment: some Turan system has cardinality `turanNumber n s r`. -/
theorem turanNumber_attains (n s r : ℕ)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) :
    ∃ H, IsTuranSystem n s r H ∧ H.card = turanNumber n s r := by
  obtain ⟨H, hH, hcard⟩ := turanNumber_mem n s r hd
  exact ⟨H, hH, hcard⟩
/-- Upper bound: the Turan number is at most the size of any system. -/
theorem turanNumber_le (n s r : ℕ) (H : Finset (Finset (Fin n)))
    (hH : IsTuranSystem n s r H) : turanNumber n s r ≤ H.card := by
  classical
  have hex : ∃ k, k ∈ realizedCounts n s r := ⟨_, _, hH, rfl⟩
  rw [turanNumber, dite_eq_left hex]
  exact Nat.find_min' hex ⟨H, hH, rfl⟩
/-- Greatest lower bound: any uniform lower bound is at most the number. -/
theorem le_turanNumber (n s r b : ℕ)
    (hb : ∀ k ∈ realizedCounts n s r, b ≤ k)
    (hd : 0 < r ∧ r < s ∧ s ≤ n) : b ≤ turanNumber n s r :=
  hb _ (turanNumber_mem n s r hd)
end TuranSystem
