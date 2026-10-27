import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.LatinSquares
open Function LatinSquares in ErdosSpencer
open LatinSquares
open Finset Real
open Real


namespace ErdosSpencer

/--
[mem_goodPerms_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LatinSquares.lean)
-/
@[path]
lemma mem_goodPerms_iff
  {n : ℕ}
  [DecidableEq α]
  {L : Fin n → Fin n → α}
  {σ : Equiv.Perm (Fin n)} :
-- imply
  σ ∈ goodPerms L ↔ Injective (fun i => L i (σ i)) := by
-- proof
  simp only [goodPerms, mem_filter, mem_univ, true_and]
  exact ⟨fun h a b hab => by_contra (fun hne => h a b hne hab),
    fun hinj i₁ i₂ hne heq => hne (hinj heq)⟩
end ErdosSpencer
/-- Lopsided LLL application underlying Erdős–Spencer: for $n \ge 2$, if every symbol of the $n \times n$ array $L$ appears at most $n/(4e)$ times, then the set of permutations producing a Latin transversal is nonempty. -/
namespace ErdosSpencer
open Real
/-- Erdős–Spencer 1991 (Theorem 6.5.11): if $L$ is an $n \times n$ array (with $n \ge 1$) in which every symbol appears at most $n/(4e)$ times, then $L$ has a Latin transversal. -/

end ErdosSpencer


-- created on 2026-10-23
