import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.HammingBall
import Lemma.Real.HammingBall
import Lean.Elab.Tactic.Omega


namespace MathlibExt.Combinatorics.Coding.HammingSpherePacking

/--
[hamming_sphere_packing_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Coding/HammingSpherePacking.lean)
-/
@[path]
lemma hamming_sphere_packing_bound
  [Fintype α] [DecidableEq α]
  {n t : ℕ}
  {C : Finset (Fin n → α)}
-- given
  (hα : 2 ≤ Fintype.card α)
  (hDist : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ → 2 * t + 1 ≤ hammingDist c₁ c₂) :
-- imply
  C.card * (∑ i ∈ Finset.range (t + 1),
    n.choose i * (Fintype.card α - 1) ^ i) ≤ (Fintype.card α) ^ n := by
-- proof
  -- The alphabet-size hypothesis records the conventional nontrivial-alphabet
  -- domain of the q-ary statement; the counting argument itself needs no lower bound on `q`.
  have _ := hα
  -- Radius-`t` balls around distinct codewords are disjoint.
  have hDisj : ∀ c₁ ∈ C, ∀ c₂ ∈ C, c₁ ≠ c₂ →
    Disjoint (Hamming.ball c₁ t) (Hamming.ball c₂ t) := by
    intro c₁ hc₁ c₂ hc₂ hne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [Hamming.mem_ball] at hy1 hy2
    have htri := hammingDist_triangle c₁ y c₂
    rw [hammingDist_comm y c₂] at htri
    have hge := hDist c₁ hc₁ c₂ hc₂ hne
    omega
  have hPair : ((↑C : Set (Fin n → α))).PairwiseDisjoint
    (fun c => Hamming.ball c t) := by
    intro c₁ hc₁ c₂ hc₂ hne
    rw [Finset.mem_coe] at hc₁ hc₂
    exact hDisj c₁ hc₁ c₂ hc₂ hne
  have hUnion : (C.biUnion fun c => Hamming.ball c t).card =
    ∑ c ∈ C, (Hamming.ball c t).card :=
    Finset.card_biUnion hPair
  -- Every ball has the same volume.
  have hEach : ∀ c ∈ C, (Hamming.ball c t).card =
    ∑ i ∈ Finset.range (t + 1),
      n.choose i * (Fintype.card α - 1) ^ i := by
    intro c _
    rw [Hamming.card_ball]
    simp only [Fintype.card_fin]
  have hSum : ∑ c ∈ C, (Hamming.ball c t).card =
    C.card * (∑ i ∈ Finset.range (t + 1),
      n.choose i * (Fintype.card α - 1) ^ i) := by
    have hcongr : (∑ c ∈ C, (Hamming.ball c t).card)
      = ∑ _x ∈ C, (∑ i ∈ Finset.range (t + 1),
        n.choose i * (Fintype.card α - 1) ^ i) :=
      Finset.sum_congr rfl hEach
    rw [hcongr, Finset.sum_const, smul_eq_mul]
  have hUniv : (Finset.univ : Finset (Fin n → α)).card =
    (Fintype.card α) ^ n := by
    rw [Finset.card_univ]
    simp [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc C.card * (∑ i ∈ Finset.range (t + 1),
    n.choose i * (Fintype.card α - 1) ^ i)
    = ∑ c ∈ C, (Hamming.ball c t).card := hSum.symm
    _ = (C.biUnion fun c => Hamming.ball c t).card := hUnion.symm
    _ ≤ (Finset.univ : Finset (Fin n → α)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = (Fintype.card α) ^ n := hUniv

end MathlibExt.Combinatorics.Coding.HammingSpherePacking


-- created on 2026-10-20
-- updated on 2026-10-23
