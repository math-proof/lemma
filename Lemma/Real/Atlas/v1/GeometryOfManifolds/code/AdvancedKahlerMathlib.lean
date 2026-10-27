import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahlerMathlib


/--
[compact_kahler_odd_betti_even_mathlib](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahlerMathlib.lean)
-/
@[path]
lemma compact_kahler_odd_betti_even_mathlib
  {n : ℕ}
  {M : CompactKahlerManifold n}
  {bd : BidegreeDecomposition n M}
  {k : ℕ}
-- given
  (hk : k % 2 = 1) :
-- imply
  ∃ (m : ℕ), bd.betti k = 2 * m := by
-- proof
  rw [bd.hodge_decomposition k]
  set f := (fun p => bd.hodge p (k - p))
  have hf : ∀ p, p ≤ k → f p = f (k - p) := by
    intro p hp
    simp only [f]
    rw [bd.conjugation_symmetry p (k - p)]
    congr 1; omega
  have ⟨j, hj⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
  subst hj
  have hlen : 2 * j + 1 + 1 = (j + 1) + (j + 1) := by omega
  rw [hlen, Finset.sum_range_add]
  suffices h : (Finset.range (j + 1)).sum (fun x => f (j + 1 + x)) =
    (Finset.range (j + 1)).sum f by
    rw [h]; exact ⟨_, (two_mul _).symm⟩
  apply Finset.sum_bij' (fun a _ => j - a) (fun a _ => j - a)
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha
    simp only [Finset.mem_range] at ha ⊢; omega
  · intro a ha
    simp only [Finset.mem_range] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha; omega
  · intro a ha
    simp only [Finset.mem_range] at ha
    have hp : j + 1 + a ≤ 2 * j + 1 := by omega
    rw [hf (j + 1 + a) hp]
    congr 1; omega


-- created on 2026-10-23
