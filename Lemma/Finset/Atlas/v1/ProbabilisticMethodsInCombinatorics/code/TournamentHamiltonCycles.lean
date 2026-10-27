import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.TournamentHamiltonCycles
open Finset Real TournamentHamiltonCycles


namespace TournamentHamiltonCycles

/--
[outDeg_pos_of_numHamiltonCycles_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/TournamentHamiltonCycles.lean)
-/
@[path]
lemma outDeg_pos_of_numHamiltonCycles_pos
  {n : ℕ}
  {T : Tournament n}
  {i : Fin n}
-- given
  (h : T.numHamiltonCycles > 0) :
-- imply
  T.outDeg i > 0 := by
-- proof
  classical
  unfold Tournament.numHamiltonCycles at h
  have hne : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ)).Nonempty :=
    Finset.card_pos.mp h
  obtain ⟨σ, hσ⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  obtain ⟨hedge, _, _⟩ := hσ
  unfold Tournament.outDeg
  exact Finset.card_pos.mpr ⟨σ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge i⟩⟩
/-- Theorem 10.2.6 (Alon 1990 for cycles). There exists $C > 0$ such that every $n$-vertex
tournament has at most $C \sqrt{n} \cdot n! / 2^n$ Hamilton cycles. -/

end TournamentHamiltonCycles


-- created on 2026-10-23
