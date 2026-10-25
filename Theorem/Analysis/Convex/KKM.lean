-- Author: @toskua, Avocado
-- Original KKM formalization by Adam Kiezun (`@akiezun`) in commit
-- `d855ffa90ad200e1ae118101768bd192d0d3c59f`; `@toskua, Avocado` authored
-- only the `Convexity.StdSimplex` representation migration.
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.Convex.KKM.Part2
/-!
# Knaster-Kuratowski-Mazurkiewicz lemma

Proved via Sperner's lemma on iterated barycentric subdivisions plus a
mesh-shrinking limit argument: fully labeled simplices at every level, a
convergent subsequence in the compact simplex (mesh `(n/(n+1))^k → 0`), and
closedness of the cover. Vertices at level `k+1` are finsets of level-`k`
vertices; validity means a nonempty chain with supports in the coordinate
set; `BdPt` is barycentric realization in `Convexity.StdSimplex`.

Primary source: B. Knaster, C. Kuratowski, S. Mazurkiewicz,
"Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe",
Fundamenta Mathematicae 14 (1929), 132–137, DOI 10.4064/fm-14-1-132-137.
-/


namespace Convex.KKM

variable {n : ℕ}

/-- Valid simplices are nonempty at every level. -/
lemma nonempty_of_valid {S : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)}, BdValid S k σ → σ.Nonempty
  | 0, _, h => h.2
  | _ + 1, _, h => h.2.2

/-- Valid simplices have cardinality at most `|S|` and at least 1. -/
lemma card_of_valid {S : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)},
      BdValid S k σ → 1 ≤ σ.card ∧ σ.card ≤ S.card := by
  intro k
  induction k with
  | zero =>
    intro σ h
    refine ⟨Finset.card_pos.mpr h.2, Finset.card_le_card h.1⟩
  | succ k ih =>
    intro σ h
    obtain ⟨hchain, hmem, hne⟩ := h
    have hpos : 1 ≤ σ.card := Finset.card_pos.mpr hne
    refine ⟨hpos, ?_⟩
    -- element cards are distinct values in {1, ..., |S|}
    have hmem' : ∀ v ∈ σ, 1 ≤ (BdFin v).card ∧ (BdFin v).card ≤ S.card :=
      fun v hv => ih (hmem v hv)
    have hinj : Set.InjOn (fun v : BdV (n := n) (k + 1) => (BdFin v).card) ↑σ := by
      intro a ha b hb hab
      by_contra hne2
      have hcomp := hchain a ha b hb
      have hlt : (BdFin a).card ≠ (BdFin b).card := by
        cases hcomp with
        | inl hsub =>
          have hss : BdFin a ⊂ BdFin b :=
            ⟨hsub, fun hle => hne2 (Finset.Subset.antisymm hsub hle)⟩
          have := Finset.card_lt_card hss
          omega
        | inr hsub =>
          have hss : BdFin b ⊂ BdFin a :=
            ⟨hsub, fun hle => hne2 (Finset.Subset.antisymm hsub hle).symm⟩
          have := Finset.card_lt_card hss
          omega
      exact hlt hab
    have himg : σ.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card) ⊆
        Finset.Icc 1 S.card := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have ha' := hmem' a ha
      exact Finset.mem_Icc.mpr ha'
    calc σ.card = (σ.image (fun v : BdV (n := n) (k + 1) =>
            (BdFin v).card)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 S.card).card := Finset.card_le_card himg
      _ = S.card := by rw [Nat.card_Icc]; omega

/-- Membership in coordinate support at level 0. -/
lemma mem_BdSupp_zero {i : BdV (n := n) 0} {j : Fin (n + 1)} :
    j ∈ BdSupp 0 i ↔ j = BdFin0 i := Finset.mem_singleton

/-- Membership in coordinate support at higher levels. -/
lemma mem_BdSupp_succ {k : ℕ} {σ : BdV (n := n) (k + 1)}
    {j : Fin (n + 1)} :
    j ∈ BdSupp (k + 1) σ ↔ ∃ v ∈ BdFin σ, j ∈ BdSupp k v :=
  Finset.mem_biUnion

/-- Singletons of members of valid sets are valid. -/
lemma valid_singleton_of_mem {S : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)} {w : BdV (n := n) k},
      BdValid S k σ → w ∈ σ → BdValid S k {w} := by
  intro k
  induction k with
  | zero =>
    intro σ w h hw
    refine ⟨?_, Finset.singleton_nonempty w⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact h.1 hw
  | succ k ih =>
    intro σ w h hw
    obtain ⟨hchain, hmem, hne⟩ := h
    refine ⟨?_, ?_, Finset.singleton_nonempty w⟩
    · intro a ha b hb
      rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
      subst ha
      subst hb
      exact Or.inl (Finset.Subset.refl _)
    · intro v hv
      rw [Finset.mem_singleton] at hv
      subst v
      exact hmem w hw

/-- Coordinate support of a valid vertex lies in the coordinate set. -/
lemma BdSupp_subset {S : Finset (Fin (n + 1))} :
    ∀ {k} {v : BdV (n := n) k}, BdValid S k {v} → BdSupp k v ⊆ S := by
  intro k
  induction k with
  | zero =>
    intro v hv j hj
    rw [mem_BdSupp_zero] at hj
    obtain rfl := hj
    exact hv.1 (Finset.mem_singleton_self _)
  | succ k ih =>
    intro v hv j hj
    rw [mem_BdSupp_succ] at hj
    obtain ⟨w, hw, hjw⟩ := hj
    obtain ⟨hchain, hmem, hne⟩ := hv
    have hvset : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
    exact ih (valid_singleton_of_mem hvset hw) hjw

/-- Barycentric coordinates vanish outside the support. -/
lemma BdPt_eq_zero_of_not_mem_supp {k : ℕ} {v : BdV (n := n) k}
    {j : Fin (n + 1)} (hj : j ∉ BdSupp k v) : BdPt k v j = 0 := by
  induction k with
  | zero =>
    change (if j = BdFin0 v then (1 : ℝ) else 0) = 0
    apply ite_eq_right
    intro hcon
    subst hcon
    exact hj (Finset.mem_singleton_self _)
  | succ k ih =>
    change (∑ w ∈ BdFin v, BdPt k w j) / ((BdFin v).card : ℝ) = 0
    have h0 : (∑ w ∈ BdFin v, BdPt k w j) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      apply ih
      intro hcon
      exact hj (mem_BdSupp_succ.mpr ⟨w, hw, hcon⟩)
    rw [h0, zero_div]

/-- Barycentric coordinates are nonnegative on valid vertices. -/
lemma BdPt_nonneg {S : Finset (Fin (n + 1))} :
    ∀ {k} {v : BdV (n := n) k},
      BdValid S k {v} → ∀ j, 0 ≤ BdPt k v j := by
  intro k
  induction k with
  | zero =>
    intro v hv j
    change 0 ≤ (if j = BdFin0 v then (1 : ℝ) else 0)
    split_ifs <;> positivity
  | succ k ih =>
    intro v hv j
    obtain ⟨hchain, hmem, hne⟩ := hv
    have hvset : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
    have hne' : (BdFin v).Nonempty := nonempty_of_valid hvset
    have hcard_pos : (0 : ℝ) < (BdFin v).card := by
      rw [Nat.cast_pos]
      exact Finset.card_pos.mpr hne'
    change 0 ≤ (∑ w ∈ BdFin v, BdPt k w j) / ((BdFin v).card : ℝ)
    apply div_nonneg _ (le_of_lt hcard_pos)
    apply Finset.sum_nonneg
    intro w hw
    exact ih (valid_singleton_of_mem hvset hw) j

/-- Barycentric coordinates sum to one on valid vertices. -/
lemma BdPt_sum {S : Finset (Fin (n + 1))} :
    ∀ {k} {v : BdV (n := n) k},
      BdValid S k {v} → ∑ j, BdPt k v j = 1 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    change (∑ j, (if j = BdFin0 v then (1 : ℝ) else 0)) = 1
    rw [Finset.sum_ite_eq']
    simp
  | succ k ih =>
    intro v hv
    obtain ⟨hchain, hmem, hne⟩ := hv
    have hvset : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
    have hne' : (BdFin v).Nonempty := nonempty_of_valid hvset
    have hcard_pos : (0 : ℝ) < (BdFin v).card := by
      rw [Nat.cast_pos]
      exact Finset.card_pos.mpr hne'
    have hsum : ∀ w ∈ BdFin v, ∑ j, BdPt k w j = 1 :=
      fun w hw => ih (valid_singleton_of_mem hvset hw)
    change (∑ j, (∑ w ∈ BdFin v, BdPt k w j) / ((BdFin v).card : ℝ)) = 1
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have hsum' : (∑ j, ∑ w ∈ BdFin v, BdPt k w j) = ((BdFin v).card : ℝ) := by
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun w hw => hsum w hw)]
      simp
    rw [hsum']
    exact mul_inv_cancel₀ (ne_of_gt hcard_pos)

end Convex.KKM
