import Mathlib
import sympy.Basic
open SimpleGraph Finset


namespace HighGirthChromatic

/--
[induce_compl_no_short_cycles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter3/HighGirthChromatic.lean)
-/
@[path]
lemma induce_compl_no_short_cycles
  {n : ℕ}
  {G : SimpleGraph (Fin n)}
  [DecidableRel G.Adj]
  {S : Finset (Fin n)}
  {g : ℕ}
-- given
  (hS : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → w.length ≤ g → ∃ u, u ∈ S ∧ u ∈ w.support.toFinset) :
-- imply
  ∀ (v : ↑(↑(Finset.univ \ S) : Set (Fin n))) (w : (G.induce (↑(Finset.univ \ S) : Set (Fin n))).Walk v v), w.IsCycle → g < w.length := by
-- proof
  set T : Set (Fin n) := ↑(Finset.univ \ S)
  set ι := Embedding.induce (G := G) T
  intro v w hw
  by_contra hle
  push Not at hle
  have hw_mapped : (w.map ι.toHom).IsCycle := hw.map ι.injective
  have hlen : (w.map ι.toHom).length = w.length := Walk.length_map _ _
  obtain ⟨u, hu_S, hu_supp⟩ := hS _ _ hw_mapped (hlen ▸ hle)
  have huT : u ∈ T := by
    have hx : u ∈ (w.map ι.toHom).support := List.mem_toFinset.mp hu_supp
    rw [Walk.support_map] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    have hι_eq : ι.toHom y = (y : Fin n) := by
      show ι y = (y : Fin n)
      simp only [ι, Embedding.comap, RelEmbedding.coe_mk, Function.Embedding.subtype_apply]
    rwa [hι_eq]
  have hunotS : u ∉ S := by
    simp only [T, Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
      true_and, Finset.mem_coe] at huT
    exact huT
  exact hunotS hu_S
/-- The probabilistic step of Erdős' construction: for every $k$ and every $g > 2$, there
is a finite graph $G$ that is not $k$-colorable and has girth greater than $g$. -/

end HighGirthChromatic


-- created on 2026-10-23
