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
import Def.Combinatorics.Young.PieriJacobiTrudi.Part31
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

/-- Key lemma: Non-intersection of LGV paths implies column-strictness of the converted paths.

    This is the fundamental connection between the two representations:
    - LGV: paths don't share any vertex (isNonIntersecting)
    - Nipat: paths satisfy column-strictness (colStrictPaths)

    The proof uses the fact that for sorted source/target vertices:
    - If paths i < j share a vertex (x, y), they would have the same height at some column
    - This violates column-strictness which requires strict ordering

    **Proof sketch:**
    Suppose paths i and j (with i < j) share a vertex (x, y).
    - Path i goes from (μᵢ - i, 1) to (λᵢ - i, N)
    - Path j goes from (μⱼ - j, 1) to (λⱼ - j, N)
    - At x-coordinate x, both paths have y-coordinate y
    - The east-step at column k in path i (where μᵢ - i + k = x) has height y
    - The east-step at column k' in path j (where μⱼ - j + k' = x) has height y
    - If μᵢ + k = μⱼ + k' (same tableau column), then heights should be strictly ordered
    - But both have height y, contradiction -/
theorem isNonIntersecting_implies_colStrictPaths (lam mu : Fin N → ℕ)
    (hlam : ∀ i j : Fin N, i ≤ j → lam j ≤ lam i)
    (hmu : ∀ i j : Fin N, i ≤ j → mu j ≤ mu i)
    (hcontained : ∀ i, mu i ≤ lam i)
    (pt : LGV.PathTuple LGV.integerLattice N
      (jacobiTrudiSourceVertex mu) (jacobiTrudiTargetVertex lam))
    (hni : pt.isNonIntersecting) :
    ∀ i j : Fin N, i < j →
      ∀ k : ℕ, ∀ hk : k < ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length,
      ∀ k' : ℕ, ∀ hk' : k' < ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length,
      mu i + k = mu j + k' →
      ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] <
        ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] := by
  -- The proof uses strong induction on j - i.
  -- For any i < j, we show h_i[k] < h_j[k'] when mu i + k = mu j + k'.
  --
  -- Base case (j = i + 1): We show that if h_i[k] ≥ h_j[k'], paths share a vertex.
  -- The key insight is that at x = (μ_i - i) + k - 1 = (μ_j - j) + k',
  -- path i is at y = h_i[k].val + 1 and path j is at y = h_j[k'].val + 1.
  -- If h_i[k] ≥ h_j[k'], then path i's y ≥ path j's y at this x-coordinate.
  -- But path j starts to the left of path i (at y = 1), so if they don't share
  -- a vertex, path j must be strictly above path i at all shared x-coordinates.
  -- This would force h_j[k'] > h_i[k], contradiction.
  --
  -- Inductive case (j > i + 1): Use transitivity through l = i + 1.
  intro i j hij k hk k' hk' hcol
  -- Use strong induction on the difference j - i
  have h_diff_pos : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
  obtain ⟨d, hd⟩ : ∃ d, j.val - i.val = d + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h_diff_pos)
  induction d using Nat.strong_induction_on generalizing i j k k' with
  | _ d ih =>
    by_cases hcons : d = 0
    · -- Base case: j = i + 1 (consecutive rows)
      subst hcons
      have hj_eq : j.val = i.val + 1 := by omega
      -- Proof by contradiction: assume h_i[k] ≥ h_j[k']
      by_contra h_not_lt
      push Not at h_not_lt
      -- We show paths share a vertex, contradicting hni
      have hij_ne : i ≠ j := Fin.ne_of_lt hij
      apply hni i j hij_ne
      -- The shared vertex is (μ_i - i, 1) - the starting point of path i.
      use ((mu i : ℤ) - (i.val : ℤ), 1)
      constructor
      · -- (μ_i - i, 1) is the start of path i
        have hstart := pt.starts i
        unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at hstart
        rw [← hstart]
        exact List.head_mem (pt.paths i).nonempty
      · -- Path j visits (μ_i - i, 1)
        -- This is the key step. We need to show that path j passes through
        -- the starting point of path i.
        --
        -- The proof is by contradiction using the discrete IVT approach.
        -- We show that if path j doesn't visit (μ_i - i, 1), then h_j[k'] > h_i[k],
        -- contradicting h_not_lt.
        --
        -- Set up: path j goes from (μ_j - j, 1) to (λ_j - j, N)
        -- Since j = i + 1 and μ is weakly decreasing, μ_j - j < μ_i - i
        -- So path j starts strictly to the left of (μ_i - i, 1)
        --
        -- Key facts:
        -- 1. Path j visits x = μ_i - i (since it starts left and ends right of this x)
        -- 2. If path j doesn't visit (μ_i - i, 1), then at x = μ_i - i, path j has y > 1
        -- 3. Since paths don't share any vertex, path j stays strictly above path i
        -- 4. At x = μ_i - i + k, this means h_j[k'] > h_i[k]
        --
        -- This contradicts h_not_lt, so path j must visit (μ_i - i, 1).
        by_contra h_not_in_j
        -- Path j's start and end
        have hstart_j := pt.starts j
        have hfinish_j := pt.finishes j
        unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at hstart_j
        unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at hfinish_j
        -- Path j starts at (μ_j - j, 1) which is strictly left of (μ_i - i, 1)
        have hmu_j_lt : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) := by
          have hmu_ij : mu j ≤ mu i := hmu i j (Fin.le_of_lt hij)
          omega
        -- Path j ends at x = λ_j - j. We need this to be ≥ μ_i - i + k.
        -- From hcol: mu i + k = mu j + k', and k' < lam j - mu j
        -- So mu i + k < lam j, hence μ_i - i + k < λ_j - j + 1
        have hlen_j : ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length = lam j - mu j := by
          have h := ((pathTupleToLatticePaths lam mu pt) j).length_eq
          have hcont_j : mu j ≤ lam j := hcontained j
          simp only [sub_sub_sub_cancel_right] at h
          omega
        have hk'_bound : k' < lam j - mu j := by rw [← hlen_j]; exact hk'
        have h_col_bound : mu i + k < lam j := by omega
        -- Now we derive the contradiction from h_not_lt.
        -- The key insight is that if path j doesn't visit (μ_i - i, 1),
        -- then path j is strictly above path i at x = μ_i - i.
        -- Since paths don't intersect, path j stays above path i.
        -- At x = μ_i - i + k, this means h_j[k'] > h_i[k].
        --
        -- The east step heights satisfy:
        -- - h_i[k] is the y-coordinate (minus 1) of path i's k-th east step
        -- - h_j[k'] is the y-coordinate (minus 1) of path j's k'-th east step
        -- - Both east steps occur at the same x-coordinate
        --
        -- Since path j is above path i at x = μ_i - i, and paths don't intersect,
        -- path j stays above path i. So at x = μ_i - i + k, y_j > y_i.
        -- This means h_j[k'].val + 1 > h_i[k].val + 1, so h_j[k'] > h_i[k].
        -- But h_not_lt says h_i[k] ≥ h_j[k'], contradiction.
        have h_heights : ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] >
            ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] := by
          -- The proof uses path_above_stays_above (the sum-based version) and
          -- lgvPathEastStepYCoords_at_x to connect eastStepHeights to actual y-coordinates.
          --
          -- Key insight: At x = μ_i - i, path i is at y = 1 (its start), while path j
          -- is at y > 1 (since it doesn't visit (μ_i - i, 1)). The sum values at these
          -- points are s_i = μ_i - i + 1 and s_j = μ_i - i + y_j > s_i.
          -- By path_above_stays_above, path j stays above path i at all later sums.
          --
          -- At x = μ_i - i + k, the east-step y-coordinates are related to the heights.
          -- By lgvPathEastStepYCoords_at_x, the y-coordinate at x = μ_i - i + k for path i
          -- is eastStepHeights[k].val + 1, and similarly for path j.
          --
          -- Since path j is above path i at x = μ_i - i, and paths don't intersect,
          -- path j stays above at x = μ_i - i + k, giving h_j[k'] > h_i[k].
          --
          -- Get the LGV paths
          let p_i := pt.paths i
          let p_j := pt.paths j
          -- Path i starts at (μ_i - i, 1)
          have hstart_i := pt.starts i
          unfold jacobiTrudiSourceVertex jacobiTrudiSourceX at hstart_i
          -- At x = μ_i - i, path i is at y = 1 (sum = μ_i - i + 1)
          -- At x = μ_i - i, path j is at y > 1 (since it doesn't visit (μ_i - i, 1))
          -- The sum for path j at x = μ_i - i is s_j = μ_i - i + y_j where y_j > 1
          -- Use path_above_stays_above with s₀ = μ_i - i + 1 (sum where path i starts)
          -- and s₁ = sum at x = μ_i - i + k
          --
          -- First, establish that path j visits x = μ_i - i at some y > 1
          have hj_visits_x₀ : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = (mu i : ℤ) - (i.val : ℤ) ∧
              (p_j.vertices.get ⟨idx, hidx⟩).2 > 1 := by
            -- Path j starts at (μ_j - j, 1) and ends at (λ_j - j, N)
            -- Since μ_j - j < μ_i - i < λ_j - j (from bounds), path j visits x = μ_i - i
            have hx_in_range : (mu j : ℤ) - (j.val : ℤ) < (mu i : ℤ) - (i.val : ℤ) ∧
                (mu i : ℤ) - (i.val : ℤ) ≤ (lam j : ℤ) - (j.val : ℤ) := by
              constructor
              · exact hmu_j_lt
              · have h1 : mu i + k < lam j := h_col_bound
                have h2 : k < lam i - mu i := by
                  have hlen_i : ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length = lam i - mu i := by
                    have h := ((pathTupleToLatticePaths lam mu pt) i).length_eq
                    have hcont_i : mu i ≤ lam i := hcontained i
                    simp only [sub_sub_sub_cancel_right] at h
                    omega
                  rw [← hlen_i]; exact hk
                omega
            -- Path j is monotone in x, so it visits all x in [start.x, finish.x]
            -- Find the first vertex with x = μ_i - i
            -- This vertex has y > 1 since (μ_i - i, 1) is not in path j
            have hbd := LGV.integerLattice_path_vertices_bounded p_j
            have hlen := LGV.integerLattice_path_length_eq p_j
            rw [hstart_j, hfinish_j] at hlen hbd
            -- The x-coordinate increases from μ_j - j to λ_j - j
            -- At some index, x = μ_i - i
            -- Use that x increases by 0 or 1 at each step (integerLattice_path_x_step)
            -- Find idx such that x = μ_i - i
            -- Since start.x < μ_i - i ≤ finish.x, such idx exists
            -- The proof uses discrete IVT on x-coordinates
            --
            -- First, find an index where x = μ_i - i using discrete IVT
            -- Define x_coord(idx) = (p_j.vertices.get idx).1
            -- At idx = 0, x = μ_j - j < μ_i - i
            -- At idx = length - 1, x = λ_j - j ≥ μ_i - i
            -- x increases by 0 or 1 at each step
            -- By IVT, there exists idx with x = μ_i - i
            have hlen_pos : 0 < p_j.vertices.length := List.length_pos_of_ne_nil p_j.nonempty
            have hlast : p_j.vertices.length - 1 < p_j.vertices.length := Nat.sub_lt hlen_pos Nat.one_pos
            -- x at start < μ_i - i
            have hx_start : (p_j.vertices.get ⟨0, hlen_pos⟩).1 < (mu i : ℤ) - (i.val : ℤ) := by
              have hstart_eq : p_j.vertices.get ⟨0, hlen_pos⟩ = p_j.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_j]
              exact hx_in_range.1
            -- x at end ≥ μ_i - i
            have hx_end : (p_j.vertices.get ⟨p_j.vertices.length - 1, hlast⟩).1 ≥ (mu i : ℤ) - (i.val : ℤ) := by
              have hfinish_eq : p_j.vertices.get ⟨p_j.vertices.length - 1, hlast⟩ = p_j.finish := by
                simp only [LGV.SimpleDigraph.Path.finish, List.getLast_eq_getElem, List.get_eq_getElem]
              rw [hfinish_eq, hfinish_j]
              exact hx_in_range.2
            -- Use discrete IVT to find the index
            -- The x-coordinate function: f(idx) = x(idx) - (μ_i - i)
            -- f(0) < 0 and f(length-1) ≥ 0
            -- |f(idx+1) - f(idx)| ≤ 1 (since x increases by 0 or 1)
            -- By IVT, there exists idx with f(idx) = 0
            let f (idx : ℕ) (hidx : idx < p_j.vertices.length) : ℤ :=
              (p_j.vertices.get ⟨idx, hidx⟩).1 - ((mu i : ℤ) - (i.val : ℤ))
            have hf_start : f 0 hlen_pos < 0 := by simp only [f]; omega
            have hf_end : f (p_j.vertices.length - 1) hlast ≥ 0 := by simp only [f]; omega
            -- Find the first index where f ≥ 0
            -- This index has f = 0 (since f increases by at most 1 and f(prev) < 0)
            have h_exists : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
                (p_j.vertices.get ⟨idx, hidx⟩).1 = (mu i : ℤ) - (i.val : ℤ) := by
              -- Use Nat.find to get the smallest index where x ≥ target
              let target : ℤ := (mu i : ℤ) - (i.val : ℤ)
              let P : ℕ → Prop := fun idx => ∃ hidx : idx < p_j.vertices.length,
                  (p_j.vertices.get ⟨idx, hidx⟩).1 ≥ target
              have hP_dec : DecidablePred P := by
                intro idx
                by_cases h : idx < p_j.vertices.length
                · exact decidable_of_iff ((p_j.vertices.get ⟨idx, h⟩).1 ≥ target)
                    ⟨fun hf => ⟨h, hf⟩, fun ⟨_, hf⟩ => hf⟩
                · exact isFalse (fun ⟨hidx, _⟩ => h hidx)
              have hP_exists : ∃ idx, P idx := ⟨p_j.vertices.length - 1, hlast, hx_end⟩
              let idx₀ := Nat.find hP_exists
              have hidx₀_lt : idx₀ < p_j.vertices.length := (Nat.find_spec hP_exists).choose
              have hx_idx₀_ge : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 ≥ target :=
                (Nat.find_spec hP_exists).choose_spec
              -- Show idx₀ > 0 (since x at 0 < target)
              have hidx₀_pos : idx₀ > 0 := by
                by_contra h
                push Not at h
                have hidx₀_eq_zero : idx₀ = 0 := Nat.eq_zero_of_le_zero h
                have h1 : (p_j.vertices.get ⟨0, hlen_pos⟩).1 ≥ target := by
                  have heq' : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 =
                             (p_j.vertices.get ⟨0, hlen_pos⟩).1 := by
                    simp only [hidx₀_eq_zero]
                  rw [← heq']; exact hx_idx₀_ge
                simp only [target] at h1
                omega
              -- At idx₀ - 1, x < target (by minimality of idx₀)
              have hidx₀_pred_lt : idx₀ - 1 < p_j.vertices.length :=
                Nat.lt_of_lt_of_le (Nat.sub_lt hidx₀_pos Nat.one_pos) (Nat.le_of_lt hidx₀_lt)
              have hx_pred_lt : (p_j.vertices.get ⟨idx₀ - 1, hidx₀_pred_lt⟩).1 < target := by
                by_contra h
                push Not at h
                have : P (idx₀ - 1) := ⟨hidx₀_pred_lt, h⟩
                have : idx₀ ≤ idx₀ - 1 := Nat.find_le this
                omega
              -- The step from idx₀ - 1 to idx₀ increases x by 0 or 1
              have hstep_idx : idx₀ - 1 + 1 < p_j.vertices.length := by omega
              have hstep := LGV.integerLattice_path_x_step p_j (idx₀ - 1) hstep_idx
              -- idx₀ - 1 + 1 = idx₀
              have heq : idx₀ - 1 + 1 = idx₀ := Nat.sub_add_cancel hidx₀_pos
              -- So x increases by 0 or 1 from idx₀ - 1 to idx₀
              -- Since x(idx₀ - 1) < target ≤ x(idx₀) and x increases by at most 1, x(idx₀) = target
              have hx_idx₀_eq : (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 = target := by
                have h1 : (p_j.vertices.get ⟨idx₀ - 1 + 1, hstep_idx⟩).1 =
                          (p_j.vertices.get ⟨idx₀, hidx₀_lt⟩).1 := by
                  simp only [Nat.sub_add_cancel hidx₀_pos]
                have h2 : (p_j.vertices.get ⟨idx₀ - 1, Nat.lt_of_succ_lt hstep_idx⟩).1 =
                          (p_j.vertices.get ⟨idx₀ - 1, hidx₀_pred_lt⟩).1 := rfl
                rcases hstep with hstep0 | hstep1
                · -- x(idx₀) = x(idx₀ - 1), but x(idx₀ - 1) < target ≤ x(idx₀), contradiction
                  rw [h1, h2] at hstep0
                  omega
                · -- x(idx₀) = x(idx₀ - 1) + 1
                  rw [h1, h2] at hstep1
                  omega
              exact ⟨idx₀, hidx₀_lt, hx_idx₀_eq⟩
            obtain ⟨idx, hidx, hx_eq⟩ := h_exists
            -- Now show y > 1 at this index
            -- If y = 1, then vertex is (μ_i - i, 1), which is not in path j
            refine ⟨idx, hidx, hx_eq, ?_⟩
            by_contra hy_le
            push Not at hy_le
            -- y ≤ 1, but y ≥ 1 (since path starts at y = 1 and y increases)
            have hy_ge : (p_j.vertices.get ⟨idx, hidx⟩).2 ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_j idx hidx
              rw [hstart_j] at hbd
              exact hbd.2.2.1
            have hy_eq : (p_j.vertices.get ⟨idx, hidx⟩).2 = 1 := by omega
            -- So vertex is (μ_i - i, 1)
            have hv_eq : p_j.vertices.get ⟨idx, hidx⟩ = ((mu i : ℤ) - (i.val : ℤ), 1) := by
              ext <;> [exact hx_eq; exact hy_eq]
            -- But (μ_i - i, 1) is not in path j
            have hmem : p_j.vertices.get ⟨idx, hidx⟩ ∈ p_j.vertices := List.get_mem p_j.vertices ⟨idx, hidx⟩
            rw [hv_eq] at hmem
            exact h_not_in_j hmem

          obtain ⟨idx_j_x₀, hidx_j_x₀, hx_j_x₀, hy_j_x₀⟩ := hj_visits_x₀
          -- Key insight for the base case (j = i + 1):
          -- At x = x₀ = μ_i - i, path i starts at y = 1, while path j is at y > 1.
          -- Since paths don't intersect, this "path j above path i" property is maintained.
          --
          -- Define x₀ (path i's starting x-coordinate) and x₁ (where we compare heights)
          let x₀ : ℤ := (mu i : ℤ) - (i.val : ℤ)
          let x₁ : ℤ := (mu i : ℤ) - (i.val : ℤ) + k
          
          -- Path i has a vertex at x₀ (its start)
          have hx₀_p_i : ∃ (idx : ℕ) (hidx : idx < p_i.vertices.length),
              (p_i.vertices.get ⟨idx, hidx⟩).1 = x₀ := by
            have hlen_pos : 0 < p_i.vertices.length := List.length_pos_of_ne_nil p_i.nonempty
            refine ⟨0, hlen_pos, ?_⟩
            have hstart_eq : p_i.vertices.get ⟨0, hlen_pos⟩ = p_i.start := by
              simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
            rw [hstart_eq, hstart_i]
          
          -- Path j has a vertex at x₀ (from hj_visits_x₀)
          have hx₀_p_j : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = x₀ := ⟨idx_j_x₀, hidx_j_x₀, hx_j_x₀⟩
          
          -- Non-intersection: path i and j share no vertices
          have hni_ij : ∀ v, v ∈ p_i.vertices → v ∉ p_j.vertices := by
            intro v hv_in_i hv_in_j
            apply hni i j hij_ne
            exact ⟨v, hv_in_i, hv_in_j⟩
          
          -- At x₀, path j's y > path i's y for ALL pairs of vertices at x₀
          -- This is the key lemma: path i at x₀ has only vertices with y ∈ {1, 2, ..., m}
          -- where m is the max y of path i at x₀. Path j at x₀ has y > 1 and disjoint
          -- from path i's y-values, so path j's y > m ≥ path i's y.
          have h_above_at_x₀ : ∀ (idx_p : ℕ) (hidx_p : idx_p < p_i.vertices.length)
              (idx_p' : ℕ) (hidx_p' : idx_p' < p_j.vertices.length),
              (p_i.vertices.get ⟨idx_p, hidx_p⟩).1 = x₀ →
              (p_j.vertices.get ⟨idx_p', hidx_p'⟩).1 = x₀ →
              (p_j.vertices.get ⟨idx_p', hidx_p'⟩).2 > (p_i.vertices.get ⟨idx_p, hidx_p⟩).2 := by
            intro idx_p hidx_p idx_p' hidx_p' hx_p hx_p'
            -- Path i at x₀ has y ≥ 1 (starts at y = 1)
            -- Path i's vertices at x₀ are consecutive y-values starting from 1
            -- Path j at x₀ has y > 1 (from hj_visits_x₀) and disjoint from path i
            -- 
            -- Key insight: at x₀ = start.x of path i, path i's vertices at x₀
            -- form a consecutive sequence {(x₀, 1), (x₀, 2), ..., (x₀, m)}.
            -- Path j's vertices at x₀ are disjoint (non-intersection) and have y > 1.
            -- So path j's y-values at x₀ are in ℕ≥2 \ {2, ..., m} = {m+1, m+2, ...}.
            -- Therefore path j's y > m ≥ path i's y at x₀.
            --
            -- The proof uses that path i at x₀ starts at y = 1 (index 0).
            have hlen_pos_i : 0 < p_i.vertices.length := List.length_pos_of_ne_nil p_i.nonempty
            have hstart_at_x₀ : (p_i.vertices.get ⟨0, hlen_pos_i⟩).1 = x₀ := by
              have hstart_eq : p_i.vertices.get ⟨0, hlen_pos_i⟩ = p_i.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_i]
            have hstart_y : (p_i.vertices.get ⟨0, hlen_pos_i⟩).2 = 1 := by
              have hstart_eq : p_i.vertices.get ⟨0, hlen_pos_i⟩ = p_i.start := by
                simp only [LGV.SimpleDigraph.Path.start, List.head_eq_getElem, List.get_eq_getElem]
              rw [hstart_eq, hstart_i]
            -- Path i's vertex at idx_p has x = x₀ and y ≥ 1
            have hy_p_ge : (p_i.vertices.get ⟨idx_p, hidx_p⟩).2 ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_i idx_p hidx_p
              rw [hstart_i] at hbd
              exact hbd.2.2.1
            -- The y-coordinate at idx_p is between 1 and some max value
            -- Use integerLattice_path_y_contiguous_at_x to show path i covers all y in [1, y_p]
            -- Since path j's vertex at idx_p' has the same x = x₀ and y > 1,
            -- and paths don't intersect, path j's y must be > path i's max y at x₀.
            --
            -- Simpler argument: path i at x₀ has consecutive y-values from 1.
            -- If path j at x₀ has y = y_j, and y_j ≤ y_p, then (x₀, y_j) is in path i
            -- (by contiguity), contradicting non-intersection.
            by_contra h_not_above
            push Not at h_not_above
            -- So y_j ≤ y_p
            let y_p := (p_i.vertices.get ⟨idx_p, hidx_p⟩).2
            let y_j := (p_j.vertices.get ⟨idx_p', hidx_p'⟩).2
            -- y_j ≥ 1 (from hy_j_x₀ we know y > 1 for the specific idx_j_x₀, but we need it for idx_p')
            have hy_j_ge : y_j ≥ 1 := by
              have hbd := LGV.integerLattice_path_vertices_bounded p_j idx_p' hidx_p'
              rw [hstart_j] at hbd
              exact hbd.2.2.1
            -- Use integerLattice_path_y_contiguous_at_x: path i covers all y in [1, y_p] at x₀
            -- Since y_j ∈ [1, y_p] (by hy_j_ge and h_not_above), (x₀, y_j) ∈ path i
            have h_contiguous := integerLattice_path_y_contiguous_at_x p_i x₀
              0 idx_p hlen_pos_i hidx_p (Nat.zero_le _) hstart_at_x₀ hx_p y_j
              (by simp only [y_j]; rw [hstart_y]; exact hy_j_ge) h_not_above
            obtain ⟨k_i, hk_i, _, _, hx_k_i, hy_k_i⟩ := h_contiguous
            -- So path i has vertex (x₀, y_j) at index k_i
            have hv_i : p_i.vertices.get ⟨k_i, hk_i⟩ = (x₀, y_j) := by
              ext <;> [exact hx_k_i; exact hy_k_i]
            -- Path j has vertex (x₀, y_j) at index idx_p'
            have hv_j : p_j.vertices.get ⟨idx_p', hidx_p'⟩ = (x₀, y_j) := by
              ext <;> [exact hx_p'; rfl]
            -- But (x₀, y_j) is in both paths, contradicting non-intersection
            have hmem_i : (x₀, y_j) ∈ p_i.vertices := by
              rw [← hv_i]; exact List.get_mem p_i.vertices ⟨k_i, hk_i⟩
            have hmem_j : (x₀, y_j) ∈ p_j.vertices := by
              rw [← hv_j]; exact List.get_mem p_j.vertices ⟨idx_p', hidx_p'⟩
            exact hni_ij (x₀, y_j) hmem_i hmem_j
          
          -- Now use paths_above_at_x_stays_above to extend to x₁
          -- First, establish that both paths visit x₁
          -- Path i visits x₁ at its k-th east step
          have hx₁_ge_x₀ : x₁ ≥ x₀ := by simp only [x₁, x₀]; omega
          
          -- Get the y-coordinates at x₁ from lgvPathEastStepYCoords_at_x
          -- For path i: the k-th east step is at x = start_x + k = μ_i - i + k = x₁
          have hk_lt_ycoords_i : k < (lgvPathEastStepYCoords p_i.vertices).length := by
            have hlen_eq : (lgvPathEastStepYCoords p_i.vertices).length = 
                ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights.length := by
              simp only [pathTupleToLatticePaths, lgvPathToLatticePath, p_i]
              simp only [lgvYCoordsToFinN, List.length_pmap]
            rw [hlen_eq]; exact hk
          have h_i_at_x₁ := lgvPathEastStepYCoords_at_x p_i k hk_lt_ycoords_i
          obtain ⟨idx_i_x₁, hidx_i_x₁, hx_i_x₁, hy_i_x₁⟩ := h_i_at_x₁
          -- Verify x-coordinate matches x₁
          have hx_i_x₁_eq : (p_i.vertices.get ⟨idx_i_x₁, hidx_i_x₁⟩).1 = x₁ := by
            rw [hx_i_x₁]
            -- p_i.start.1 = (mu i : ℤ) - (i.val : ℤ) from hstart_i
            have hstart_x : p_i.start.1 = (mu i : ℤ) - (i.val : ℤ) := by
              simp only [p_i, hstart_i]
            rw [hstart_x]
          
          -- For path j: the k'-th east step is at x = start_x + k' = μ_j - j + k'
          -- We need to show this equals x₁ = μ_i - i + k
          -- From hcol: mu i + k = mu j + k', so μ_i - i + k = μ_j - j + k' + (j - i)
          -- Since j = i + 1, we get μ_i - i + k = μ_j - j + k' + 1
          -- So path j's k'-th east step is at x = x₁ - 1, and AFTER the east step, path j is at x₁
          have hk'_lt_ycoords_j : k' < (lgvPathEastStepYCoords p_j.vertices).length := by
            have hlen_eq : (lgvPathEastStepYCoords p_j.vertices).length = 
                ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length := by
              simp only [pathTupleToLatticePaths, lgvPathToLatticePath, p_j]
              simp only [lgvYCoordsToFinN, List.length_pmap]
            rw [hlen_eq]; exact hk'
          have h_j_at_kprime := lgvPathEastStepYCoords_at_x p_j k' hk'_lt_ycoords_j
          obtain ⟨idx_j_kprime, hidx_j_kprime, hx_j_kprime, hy_j_kprime⟩ := h_j_at_kprime
          -- Path j's k'-th east step starts at x = μ_j - j + k'
          have hx_j_kprime_val : (p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩).1 = 
              (mu j : ℤ) - (j.val : ℤ) + k' := by
            rw [hx_j_kprime]
            have hstart_x : p_j.start.1 = (mu j : ℤ) - (j.val : ℤ) := by
              simp only [p_j, hstart_j]
            rw [hstart_x]
          -- The x-coordinate where path j's k'-th east step starts
          -- From hcol: mu i + k = mu j + k'
          -- So μ_j - j + k' = μ_j + k' - j = (μ_i + k) - j = μ_i + k - (i + 1) = μ_i - i + k - 1 = x₁ - 1
          have hx_j_eq_x₁_minus_1 : (mu j : ℤ) - (j.val : ℤ) + k' = x₁ - 1 := by
            simp only [x₁]
            have h1 : (mu i : ℕ) + k = (mu j : ℕ) + k' := hcol
            have h2 : j.val = i.val + 1 := hj_eq
            omega
          -- After the east step, path j is at x = x₁
          -- The east step increases x by 1, so the next vertex is at x = x₁
          -- Use lgvPathEastStepYCoords_at_x_is_east_step to get the next vertex
          have hidx_j_next : idx_j_kprime + 1 < p_j.vertices.length := by
            -- The k'-th east step is not the last step (path ends at y = N, not at this east step)
            -- Actually, we need to show idx_j_kprime + 1 < length
            -- This follows from the fact that there are more vertices after the east step
            -- The path ends at (λ_j - j, N), and the k'-th east step is at x = x₁ - 1 < λ_j - j
            -- So there are more vertices after this east step
            have hfinish_x : p_j.finish.1 = (lam j : ℤ) - (j.val : ℤ) := by
              rw [hfinish_j]
            have hx_lt_finish : (p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩).1 < p_j.finish.1 := by
              rw [hx_j_kprime_val, hfinish_x, hx_j_eq_x₁_minus_1]
              simp only [x₁]
              -- Need: μ_i - i + k - 1 < λ_j - j
              -- From h_col_bound: mu i + k < lam j
              -- So μ_i + k < λ_j, hence μ_i - i + k < λ_j - i = λ_j - j + (j - i) = λ_j - j + 1
              -- So μ_i - i + k - 1 < λ_j - j
              omega
            -- If idx_j_kprime is the last index, then the vertex is the finish
            by_contra h_last
            push Not at h_last
            -- h_last : p_j.vertices.length ≤ idx_j_kprime + 1
            -- We know idx_j_kprime < p_j.vertices.length (from hidx_j_kprime)
            -- So idx_j_kprime + 1 ≤ p_j.vertices.length
            -- Combined with h_last, we get idx_j_kprime + 1 = p_j.vertices.length
            have hidx_eq_last : idx_j_kprime = p_j.vertices.length - 1 := by
              have h1 : idx_j_kprime + 1 ≤ p_j.vertices.length := hidx_j_kprime
              have h2 : p_j.vertices.length ≤ idx_j_kprime + 1 := h_last
              omega
            have hfinish_eq : p_j.vertices.get ⟨idx_j_kprime, hidx_j_kprime⟩ = p_j.finish := by
              simp only [LGV.SimpleDigraph.Path.finish, List.getLast_eq_getElem, List.get_eq_getElem]
              congr 1
            rw [hfinish_eq] at hx_lt_finish
            exact (lt_irrefl _ hx_lt_finish)
          have h_east_step := lgvPathEastStepYCoords_at_x_is_east_step p_j k' hk'_lt_ycoords_j
            idx_j_kprime hidx_j_kprime hx_j_kprime hy_j_kprime hidx_j_next
          -- The next vertex is at x = x₁ with the same y-coordinate
          have hx_j_next : (p_j.vertices.get ⟨idx_j_kprime + 1, hidx_j_next⟩).1 = x₁ := by
            rw [h_east_step.1, hx_j_kprime_val, hx_j_eq_x₁_minus_1]
            ring
          have hy_j_next : (p_j.vertices.get ⟨idx_j_kprime + 1, hidx_j_next⟩).2 = 
              (lgvPathEastStepYCoords p_j.vertices)[k'] := by
            rw [h_east_step.2, hy_j_kprime]
          
          -- Now apply paths_above_at_x_stays_above
          have hx₁_p_i : ∃ (idx : ℕ) (hidx : idx < p_i.vertices.length),
              (p_i.vertices.get ⟨idx, hidx⟩).1 = x₁ := ⟨idx_i_x₁, hidx_i_x₁, hx_i_x₁_eq⟩
          have hx₁_p_j : ∃ (idx : ℕ) (hidx : idx < p_j.vertices.length),
              (p_j.vertices.get ⟨idx, hidx⟩).1 = x₁ := ⟨idx_j_kprime + 1, hidx_j_next, hx_j_next⟩
          
          have h_above_at_x₁ := paths_above_at_x_stays_above p_i p_j hni_ij x₀ hx₀_p_i hx₀_p_j
            h_above_at_x₀ x₁ hx₁_ge_x₀ hx₁_p_i hx₁_p_j
          
          -- Apply to our specific indices
          have h_y_comparison := h_above_at_x₁ idx_i_x₁ hidx_i_x₁ (idx_j_kprime + 1) hidx_j_next
            hx_i_x₁_eq hx_j_next
          -- h_y_comparison : y_j > y_i at x₁
          -- y_i = lgvPathEastStepYCoords p_i.vertices [k] = eastStepHeights[k].val + 1
          -- y_j = lgvPathEastStepYCoords p_j.vertices [k'] = eastStepHeights[k'].val + 1
          
          -- Convert to eastStepHeights comparison
          -- eastStepHeights[k] = lgvYCoordsToFinN (lgvPathEastStepYCoords ...) [k]
          -- lgvYCoordsToFinN maps y to (y - 1).toNat as Fin N
          -- So eastStepHeights[k].val = (lgvPathEastStepYCoords ...)[k] - 1
          simp only [pathTupleToLatticePaths, lgvPathToLatticePath] at hk hk' ⊢
          -- Need to show: eastStepHeights[k'] > eastStepHeights[k]
          -- i.e., (lgvYCoordsToFinN ...)[k'].val > (lgvYCoordsToFinN ...)[k].val
          -- i.e., (lgvPathEastStepYCoords p_j.vertices)[k'] - 1 > (lgvPathEastStepYCoords p_i.vertices)[k] - 1
          -- i.e., (lgvPathEastStepYCoords p_j.vertices)[k'] > (lgvPathEastStepYCoords p_i.vertices)[k]
          -- This follows from h_y_comparison since y_i = ycoords[k] and y_j = ycoords[k']
          rw [hy_i_x₁] at h_y_comparison
          rw [hy_j_next] at h_y_comparison
          -- h_y_comparison : (lgvPathEastStepYCoords p_j.vertices)[k'] > (lgvPathEastStepYCoords p_i.vertices)[k]
          -- Convert to Fin comparison
          have hfinish_i := pt.finishes i
          unfold jacobiTrudiTargetVertex jacobiTrudiTargetX at hfinish_i
          have hbnd_i : ∀ y ∈ lgvPathEastStepYCoords p_i.vertices, 1 ≤ y ∧ y ≤ N := by
            intro y hy
            have hbnd := lgvPathEastStepYCoords_bounded p_i.vertices p_i.nonempty p_i.arcs_valid y hy
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart_i hfinish_i
            rw [hstart_i, hfinish_i] at hbnd
            simp at hbnd
            exact hbnd
          have hbnd_j : ∀ y ∈ lgvPathEastStepYCoords p_j.vertices, 1 ≤ y ∧ y ≤ N := by
            intro y hy
            have hbnd := lgvPathEastStepYCoords_bounded p_j.vertices p_j.nonempty p_j.arcs_valid y hy
            simp only [LGV.SimpleDigraph.Path.start, LGV.SimpleDigraph.Path.finish] at hstart_j hfinish_j
            rw [hstart_j, hfinish_j] at hbnd
            simp at hbnd
            exact hbnd
          have hk_mem : (lgvPathEastStepYCoords p_i.vertices)[k] ∈ lgvPathEastStepYCoords p_i.vertices :=
            List.getElem_mem hk_lt_ycoords_i
          have hk'_mem : (lgvPathEastStepYCoords p_j.vertices)[k'] ∈ lgvPathEastStepYCoords p_j.vertices :=
            List.getElem_mem hk'_lt_ycoords_j
          have hbnd_k := hbnd_i _ hk_mem
          have hbnd_k' := hbnd_j _ hk'_mem
          -- The Fin values are (y - 1).toNat
          simp only [lgvYCoordsToFinN, List.getElem_pmap]
          -- Goal: Fin.mk ((ycoords_j[k'] - 1).toNat) _ > Fin.mk ((ycoords_i[k] - 1).toNat) _
          simp only [Fin.lt_def]
          -- Goal: (ycoords_j[k'] - 1).toNat > (ycoords_i[k] - 1).toNat
          have h1 : ((lgvPathEastStepYCoords p_i.vertices)[k] - 1).toNat = 
              (lgvPathEastStepYCoords p_i.vertices)[k].toNat - 1 := by
            have hge : (lgvPathEastStepYCoords p_i.vertices)[k] ≥ 1 := hbnd_k.1
            omega
          have h2 : ((lgvPathEastStepYCoords p_j.vertices)[k'] - 1).toNat = 
              (lgvPathEastStepYCoords p_j.vertices)[k'].toNat - 1 := by
            have hge : (lgvPathEastStepYCoords p_j.vertices)[k'] ≥ 1 := hbnd_k'.1
            omega
          rw [h1, h2]
          omega

        -- Now derive contradiction
        exact absurd h_heights (not_lt.mpr h_not_lt)
    · -- Inductive case: j > i + 1
      -- Use the intermediate row l = i + 1
      have h_j_gt : j.val > i.val + 1 := by omega
      have hl_lt_N : i.val + 1 < N := by
        have := j.is_lt
        omega
      let l : Fin N := ⟨i.val + 1, hl_lt_N⟩
      -- k_l = μ_i + k - μ_l is the index for row l at the same tableau column
      have hmu_l : mu l ≤ mu i := hmu i l (Fin.le_of_lt (by simp only [l, Fin.lt_def]; omega : i < l))
      have hlam_l : lam j ≤ lam l := hlam l j (by simp only [l, Fin.le_iff_val_le_val]; omega)
      let k_l : ℕ := mu i + k - mu l
      have hk_l_eq : mu l + k_l = mu i + k := by
        show mu l + (mu i + k - mu l) = mu i + k
        omega
      -- Verify k_l is a valid index
      have hk_l_lt : k_l < ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights.length := by
        -- k_l = mu i + k - mu l < lam l - mu l
        -- This follows from mu i + k = mu j + k' < lam j ≤ lam l
        -- First establish that length = lam l - mu l
        have hlen_l : ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights.length = lam l - mu l := by
          have h := ((pathTupleToLatticePaths lam mu pt) l).length_eq
          -- h : length = ((lam l : ℤ) - l.val - ((mu l : ℤ) - l.val)).toNat
          have hcont_l : mu l ≤ lam l := hcontained l
          simp only [sub_sub_sub_cancel_right] at h
          omega
        rw [hlen_l]
        -- Now goal is k_l < lam l - mu l
        -- From hk' : k' < length_j = lam j - mu j
        have hlen_j : ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights.length = lam j - mu j := by
          have h := ((pathTupleToLatticePaths lam mu pt) j).length_eq
          have hcont_j : mu j ≤ lam j := hcontained j
          simp only [sub_sub_sub_cancel_right] at h
          omega
        have hk'_bound : k' < lam j - mu j := by rw [← hlen_j]; exact hk'
        have h1 : mu j + k' < lam j := by omega
        have h2 : mu i + k < lam j := by omega
        have h3 : mu i + k ≤ lam l := Nat.le_of_lt (Nat.lt_of_lt_of_le h2 hlam_l)
        show k_l < lam l - mu l
        simp only [k_l]
        omega
      -- Apply IH for (i, l) with d' = 0 < d
      have h_i_lt_l : i < l := by
        simp only [l, Fin.lt_def]
        omega
      have h_d1_pos : 0 < l.val - i.val := by simp [l]
      have h_d1_eq : l.val - i.val = 0 + 1 := by simp [l]
      have h1 : ((pathTupleToLatticePaths lam mu pt) i).eastStepHeights[k] <
          ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights[k_l] := by
        have h_d1_lt : 0 < d := by omega
        exact ih 0 h_d1_lt i l h_i_lt_l k hk k_l hk_l_lt hk_l_eq.symm h_d1_pos h_d1_eq
      -- Apply IH for (l, j) with d' = j - l - 1 < d
      have h_l_lt_j : l < j := by simp [l]; exact h_j_gt
      have h_d2_pos : 0 < j.val - l.val := Nat.sub_pos_of_lt h_l_lt_j
      have h_d2_eq : j.val - l.val = (d - 1) + 1 := by simp [l]; omega
      have h_d2_lt : d - 1 < d := Nat.sub_lt (by omega : 0 < d) Nat.one_pos
      have hcol_l : mu l + k_l = mu j + k' := by rw [hk_l_eq, hcol]
      have h2 : ((pathTupleToLatticePaths lam mu pt) l).eastStepHeights[k_l] <
          ((pathTupleToLatticePaths lam mu pt) j).eastStepHeights[k'] := by
        exact ih (d - 1) h_d2_lt l j h_l_lt_j k_l hk_l_lt k' hk' hcol_l h_d2_pos h_d2_eq
      -- Combine by transitivity
      exact Fin.lt_trans h1 h2

end SymmetricFunctions
