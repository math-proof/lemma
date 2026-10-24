/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/RestrictedGaussianPartition.lean -/

import sympy.atlas.Combinatorics.RestrictedGaussianPartition
import Lemma.Finset.RestrictedGaussianPartition
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Basic

open MetaMathlibExt

-- q = 1 is rejected: 1 is not a prime power.
example : ¬ IsRestrictedGaussianPartition 1 1 ⟨[1], by decide⟩ := by
  rintro ⟨hprime, -, -⟩
  exact notPrimePowOne hprime

-- n = 0 is rejected.
example : ¬ IsRestrictedGaussianPartition 2 0 ⟨[], by decide⟩ := by
  rintro ⟨-, h0, -⟩
  exact absurd h0 (by decide)

-- Smallest basic ancestor with no branches is accepted.
example : IsRestrictedGaussianPartition 2 1 ⟨[1], by decide⟩ :=
  ⟨isPrimePowTwo, by decide, [{d := 1, m := 1}], [[]], by decide, by decide,
    by decide, [[1]], by decide, by decide, by decide, by decide, rfl⟩

-- A split level with zero right dimension is rejected.
example : ¬ ChainHeadValid 2 [{d := 2, m := 2}] 0 {a := 1, b := 0, c := 1} := by
  decide

-- A split level whose parent mismatches the block root is rejected.
example : ¬ ChainHeadValid 2 [{d := 4, m := 2}] 0 {a := 1, b := 1, c := 1} := by
  decide

-- Three-level chain with strictly decreasing lefts: consecutive linkage holds,
-- while the first and last levels disagree (2 ≠ 3), so an all-pairs check fails.
example : ChainAdjValid [{a := 3, b := 1, c := 1}, {a := 2, b := 1, c := 1},
    {a := 1, b := 1, c := 1}] := by
  decide

-- A chain with a broken consecutive link is rejected.
example : ¬ ChainAdjValid [{a := 3, b := 1, c := 1}, {a := 5, b := 1, c := 1}] := by
  decide

-- The three-level chain is realized with all intermediate lists descending.
example : IsRestrictedGaussianPartition 2 8
    ⟨List.replicate 16 4 ++ List.replicate 15 1, by decide⟩ :=
  ⟨isPrimePowTwo, by decide, [{d := 4, m := 2}],
    [[{a := 3, b := 1, c := 1}, {a := 2, b := 1, c := 1},
      {a := 1, b := 1, c := 1}]],
    by decide, by decide, by decide,
    [List.replicate 16 4 ++ List.replicate 15 1],
    by decide, by decide, by decide, by decide, rfl⟩

-- First-count bound on a later singleton block: accepted exactly at q^u - 1 = 7.
example : ChainHeadValid 2 [{d := 3, m := 1}, {d := 2, m := 1}] 1
    {a := 1, b := 1, c := 7} := by
  decide

-- ... and rejected above it.
example : ¬ ChainHeadValid 2 [{d := 3, m := 1}, {d := 2, m := 1}] 1
    {a := 1, b := 1, c := 8} := by
  decide

-- The at-bound first split is realized with descending intermediate lists.
example : IsRestrictedGaussianPartition 2 5
    ⟨[3, 2] ++ List.replicate 21 1, by decide⟩ :=
  ⟨isPrimePowTwo, by decide, [{d := 3, m := 1}, {d := 2, m := 1}],
    [[], [{a := 1, b := 1, c := 7}]],
    by decide, by decide, by decide,
    [[3], [2] ++ List.replicate 21 1],
    by decide, by decide, by decide, by decide, rfl⟩

-- Arithmetic head conditions hold here ...
example : ChainHeadValid 2 [{d := 3, m := 2}, {d := 2, m := 1}] 0
    {a := 2, b := 1, c := 1} := by
  decide

-- ... but the intermediate global list is not descending, so the stage is rejected.
example : ¬ ((stageGlobalDims 2 [{d := 3, m := 2}, {d := 2, m := 1}]
    [[{a := 2, b := 1, c := 1}], []] [[], []] 0 0).all
    (fun g => decide (g.Pairwise (fun a b : Nat => a ≥ b))) = true) := by
  decide
