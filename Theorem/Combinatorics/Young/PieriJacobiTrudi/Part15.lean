/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.matrices.determinants.LGV2
import Def.Combinatorics.Young.OmegaInvolution.Part2
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Lemma.Matrix.LGV2
import Lemma.Partition.NPartition
import Def.Combinatorics.Young.PieriJacobiTrudi.Part27
open Finset BigOperators Matrix MvPolynomial

/-!
# The Pieri Rules and Jacobi-Trudi Identities

This file formalizes the Pieri rules for multiplying Schur polynomials by complete
homogeneous or elementary symmetric polynomials, and the Jacobi-Trudi identities
expressing skew Schur polynomials as determinants.

## Main definitions

* `NPartition`: An N-partition is a weakly decreasing N-tuple of nonnegative integers
* `NPartition.IsTranspose`: Predicate asserting that two partitions are transposes
* `SkewPartition`: A skew partition λ/μ is a pair of partitions with μ ⊆ λ
* `SkewPartition.isHorizontalStrip`: A skew partition is a horizontal strip if no two
  boxes in Y(λ/μ) lie in the same column
* `SkewPartition.isVerticalStrip`: A skew partition is a vertical strip if no two
  boxes in Y(λ/μ) lie in the same row
* `SkewPartition.isHorizontalNStrip`: A horizontal n-strip has exactly n boxes
* `SkewPartition.isVerticalNStrip`: A vertical n-strip has exactly n boxes
* `isHorizontalStripFun`: Canonical unbundled horizontal strip predicate with `(lam, mu)` order
* `isVerticalStripFun`: Canonical unbundled vertical strip predicate with `(lam, mu)` order
* `SSYT`: A semistandard Young tableau of shape λ
* `SkewSSYT`: A semistandard Young tableau of skew shape λ/μ
* `LatticePath`: A lattice path in ℤ² using north and east steps
* `Nipat`: A non-intersecting path tuple (for LGV lemma connection)

## Main results

* `pieri_horizontal`: h_n · s_μ = ∑_{λ/μ is horizontal n-strip} s_λ (Theorem thm.sf.pieri(a))
* `pieri_vertical`: e_n · s_μ = ∑_{λ/μ is vertical n-strip} s_λ (Theorem thm.sf.pieri(b))
* `horizontalStrip_iff_entries`: Characterization of horizontal strips via partition entries
    (Proposition prop.sf.strips.entries(a))
* `verticalStrip_iff_entries`: Characterization of vertical strips via partition entries
    (Proposition prop.sf.strips.entries(b))
* `jacobiTrudi_h`: s_{λ/μ} = det(h_{λᵢ - μⱼ - i + j}) (Theorem thm.sf.jt-h)
* `jacobiTrudi_e`: s_{λ/μ} = det(e_{λᵢᵗ - μⱼᵗ - i + j}) (Theorem thm.sf.jt-e)

## References

* Source: AlgebraicCombinatorics/tex/SymmetricFunctions/PieriJacobiTrudi.tex
* [Stanley, *Enumerative Combinatorics, Vol. 2*][Stanley-EC2]
* [Grinberg-Reiner, *Hopf algebras in combinatorics*][GriRei]

## Implementation notes

We work with N-partitions as length-N lists of weakly decreasing nonnegative integers.
Schur polynomials are defined via semistandard Young tableaux (SSYT).
The Jacobi-Trudi identities are proved using the Lindström-Gessel-Viennot lemma
(see AlgebraicCombinatorics/Determinants/LGV2.lean).

For h_n and e_n with negative n, we use the convention h_n = 0 and e_n = 0.

Note: In the source, M is the length of the partition tuples (for Jacobi-Trudi),
while N is the number of variables (entries in tableaux come from [N]).
We use a single parameter N for simplicity in this formalization.

### Strip Definition Conventions

There are three representations for horizontal/vertical strip predicates:

1. **Bundled (`SkewPartition.isHorizontalStrip`)**: Takes a `SkewPartition N` directly.
   Use when working with bundled skew partitions.

2. **Unbundled canonical (`isHorizontalStripFun`)**: Takes `(lam mu : Fin N → ℕ)` with
   argument order matching the mathematical notation λ/μ. **Preferred for new code.**

See `SkewPartition.isHorizontalStrip_iff_isHorizontalStripFun` for the equivalence lemma.
-/


namespace SymmetricFunctions

variable {N : ℕ} {R : Type*} [CommRing R]

/-- Two nipats with equal paths are equal. -/
theorem Nipat.eq_of_paths_eq {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np1 np2 : Nipat lam mu hlam hmu hcontained)
    (h : np1.paths = np2.paths) : np1 = np2 := by
  obtain ⟨p1, ni1⟩ := np1
  obtain ⟨p2, ni2⟩ := np2
  simp only at h
  subst h
  rfl

/-- ssytToNipat is a left inverse of nipatToSSYT. -/
theorem ssytToNipat_nipatToSSYT {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) :
    ssytToNipat (nipatToSSYT np) = np := by
  apply Nipat.eq_of_paths_eq
  funext i
  apply LatticePath.ext
  simp only [ssytToNipat, nipatToSSYT, mkLatticePathFromEntries]
  -- Need to show: List.ofFn (fun k => (np.paths i).eastStepHeights[k]) = (np.paths i).eastStepHeights
  have hlen : (np.paths i).eastStepHeights.length = lam i - mu i := by
    rw [(np.paths i).length_eq]
    simp only [sub_sub_sub_cancel_right]
    have h : mu i ≤ lam i := hcontained i
    omega
  -- The key is that List.ofFn of getElem gives back the original list
  -- We need to show the LHS equals the RHS by showing they have the same elements
  apply List.ext_getElem
  · simp only [List.length_ofFn, hlen]
  · intro n h1 h2
    simp only [List.getElem_ofFn, List.get_eq_getElem]

/-- The length of path i's eastStepHeights equals lam i - mu i. -/
theorem nipat_path_length {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) (i : Fin N) :
    (np.paths i).eastStepHeights.length = lam i - mu i := by
  rw [(np.paths i).length_eq]
  simp only [sub_sub_sub_cancel_right]
  have h : mu i ≤ lam i := hcontained i
  omega

/-- Specification lemma for nipatToSSYT: the entries of row i are the heights
    of the east-steps in path i. This captures the key property of the bijection. -/
theorem nipatToSSYT_entries {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (np : Nipat lam mu hlam hmu hcontained) (i : Fin N) (k : Fin (lam i - mu i)) :
    (nipatToSSYT np).entries i k = (np.paths i).eastStepHeights.get ⟨k.val, by
      rw [nipat_path_length np i]; exact k.isLt⟩ := by
  simp only [nipatToSSYT, List.get_eq_getElem]

/-- Specification lemma for ssytToNipat: the east-step heights of path i are the entries
    of row i of the tableau. This is the inverse specification to nipatToSSYT_entries. -/
theorem ssytToNipat_paths {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) (i : Fin N) (k : Fin (lam i - mu i)) :
    ((ssytToNipat T).paths i).eastStepHeights.get ⟨k.val, by
      rw [nipat_path_length (ssytToNipat T) i]; exact k.isLt⟩ = T.entries i k := by
  simp only [ssytToNipat, mkLatticePathFromEntries, List.get_ofFn]
  congr 1

/-- nipatToSSYT is a left inverse of ssytToNipat. -/
theorem nipatToSSYT_ssytToNipat {lam mu : Fin N → ℕ}
    {hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i}
    {hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i}
    {hcontained : ∀ i, mu i ≤ lam i}
    (T : SkewSSYT ⟨⟨lam, hlam⟩, ⟨mu, hmu⟩, fun i => hcontained i⟩) :
    nipatToSSYT (ssytToNipat T) = T := by
  apply SkewSSYT.eq_of_entries_eq
  funext i k
  rw [nipatToSSYT_entries, ssytToNipat_paths]

end SymmetricFunctions
