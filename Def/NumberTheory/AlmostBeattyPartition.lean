/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AlmostBeattyPartition.lean -/

import Mathlib.NumberTheory.Rayleigh
/-!
Source provenance for concept `jis_sem_329070e9cea40082f4048ff4`
("almost Beatty partition").

Source: `https://cs.uwaterloo.ca/journals/JIS/VOL22/Hildebrand/hilde2.tex`
File SHA-256: `293500514025c31a4932039c6c352c549b00ddaa4700be115c59174661a03818`
Source blocks: lines 350-425 with
SHA-256 `2e8d7075e9b98c40d79c1f9222b5d7067df1d4d2ee1d33c2fa7174096c71806c`,
and lines 441-464 with
SHA-256 `687ff2ae1a163c823a339681502fbd6703a10be1922252fba6893f74741a5957`.
-/


namespace MetaMathlibExt

/-- The natural-valued Beatty term with slope `1 / α`, obtained from Mathlib's
integer-valued `beattySeq`.
Frozen source statements: `jis_3a6643107cb0f496a9559012`,
`jis_74d8835ba8df562bb5834fef`, `jis_8d72c1833a8a5da5a1a319c0`,
`jis_9c431d0d610f8a075ea0cb13`, `jis_aac0e146b36de598ccb32fd6`,
`jis_c2877cfd93d3493ab5d68e84`, and `jis_ec4d65fd2ab77c1aec768d61`. -/
noncomputable def beattyTerm (n : { n : ℕ // 0 < n }) (α : ℝ) : ℕ :=
  (beattySeq (1 / α) (n.val : ℤ)).toNat

/-- Almost-Beatty predicate for concept `jis_sem_329070e9cea40082f4048ff4`:
a strictly increasing sequence of positive integers within a uniform natural
bound of the Beatty term.
Frozen source statements: `jis_3a6643107cb0f496a9559012`,
`jis_74d8835ba8df562bb5834fef`, `jis_8d72c1833a8a5da5a1a319c0`,
`jis_9c431d0d610f8a075ea0cb13`, `jis_aac0e146b36de598ccb32fd6`,
`jis_c2877cfd93d3493ab5d68e84`, and `jis_ec4d65fd2ab77c1aec768d61`. -/
def IsAlmostBeattySequence (s : { n : ℕ // 0 < n } → ℕ) (α : ℝ) : Prop :=
  0 < α ∧ α < 1 ∧ StrictMono s ∧
    (∀ n, 0 < s n) ∧
      ∃ B : ℕ, ∀ n, ((s n : ℤ) - (beattyTerm n α : ℤ)).natAbs ≤ B

/-- Three-way partition predicate for concept `jis_sem_329070e9cea40082f4048ff4`:
pairwise disjoint ranges together with exact coverage of the positive naturals.
Frozen source statements: `jis_3a6643107cb0f496a9559012`,
`jis_74d8835ba8df562bb5834fef`, `jis_8d72c1833a8a5da5a1a319c0`,
`jis_9c431d0d610f8a075ea0cb13`, `jis_aac0e146b36de598ccb32fd6`,
`jis_c2877cfd93d3493ab5d68e84`, and `jis_ec4d65fd2ab77c1aec768d61`. -/
def IsPositiveNatThreeWayPartition (s1 s2 s3 : { n : ℕ // 0 < n } → ℕ) : Prop :=
  (∀ m n, s1 m ≠ s2 n) ∧
    (∀ m n, s1 m ≠ s3 n) ∧
      (∀ m n, s2 m ≠ s3 n) ∧
        ∀ k : ℕ, (∃ n, s1 n = k ∨ s2 n = k ∨ s3 n = k) ↔ 0 < k

/-- Almost-Beatty partition for concept `jis_sem_329070e9cea40082f4048ff4`:
three almost-Beatty sequences whose ranges partition the positive naturals.
Frozen source statements: `jis_3a6643107cb0f496a9559012`,
`jis_74d8835ba8df562bb5834fef`, `jis_8d72c1833a8a5da5a1a319c0`,
`jis_9c431d0d610f8a075ea0cb13`, `jis_aac0e146b36de598ccb32fd6`,
`jis_c2877cfd93d3493ab5d68e84`, and `jis_ec4d65fd2ab77c1aec768d61`. -/
def IsAlmostBeattyPartition (s1 s2 s3 : { n : ℕ // 0 < n } → ℕ) (α1 α2 α3 : ℝ) : Prop :=
  IsAlmostBeattySequence s1 α1 ∧
    IsAlmostBeattySequence s2 α2 ∧
      IsAlmostBeattySequence s3 α3 ∧ IsPositiveNatThreeWayPartition s1 s2 s3

end MetaMathlibExt
