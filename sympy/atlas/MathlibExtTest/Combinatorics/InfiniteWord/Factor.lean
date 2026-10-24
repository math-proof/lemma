/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/Factor.lean -/


import sympy.atlas.Combinatorics.InfiniteWord.Factor
import Lemma.Finset.InfiniteWord.Factor
import Lean.Elab.Tactic.Omega

example (u : ℕ → Bool) :
    InfiniteWord.factor u 0 37 = fun i : Fin 0 => i.elim0 := by
  apply Subsingleton.elim

example (u : ℕ → Bool) :
    InfiniteWord.initial u 0 = fun i : Fin 0 => i.elim0 := by
  apply Subsingleton.elim

example (u : ℕ → Bool) : InfiniteWord.factor u 3 2 ⟨1, by decide⟩ = u 3 := by
  rfl

example (u : ℕ → Bool) (k : ℕ) :
    InfiniteWord.initial u k ∈ InfiniteWord.factorSet u k :=
  InfiniteWord.initial_mem_factorSet u k

example (u : ℕ → Bool) (k : ℕ) : (InfiniteWord.factorSet u k).Finite :=
  InfiniteWord.finite_factorSet u k

example (u : ℕ → Bool) (i k : ℕ) :
    List.ofFn (InfiniteWord.factor u k i) = InfiniteWord.factorList u k i := by
  rfl

example (u : ℕ → Bool) (i : ℕ) : InfiniteWord.factorList u 0 i = [] := by
  rfl

example : InfiniteWord.factorList (fun n : ℕ => n) 3 2 = [2, 3, 4] := by
  decide

example (u : ℕ → Bool) : InfiniteWord.IsFactor [] u :=
  InfiniteWord.isFactor_nil u

example (u : ℕ → Bool) : ¬InfiniteWord.IsNonemptyFactor [] u :=
  InfiniteWord.not_isNonemptyFactor_nil u

example (u : ℕ → Bool) (k : ℕ) (v : Fin k → Bool) :
    InfiniteWord.IsFactor (List.ofFn v) u ↔
      v ∈ InfiniteWord.factorSet u k :=
  InfiniteWord.isFactor_ofFn_iff_mem_factorSet v u

example (u : ℕ → Bool) (i k : ℕ) (hk : 0 < k) :
    InfiniteWord.IsNonemptyFactor (InfiniteWord.factorList u k i) u := by
  rw [InfiniteWord.isNonemptyFactor_iff_isFactor_and_ne_nil]
  refine ⟨?_, (InfiniteWord.isFactor_iff_exists_factorList _ _).2 ⟨i, ?_⟩⟩
  · intro h
    have := congrArg List.length h
    simp at this
    omega
  · rw [InfiniteWord.factorList_length]

example : InfiniteWord.IsNonemptyFactor [2, 3, 4] (fun n : ℕ => n) :=
  (InfiniteWord.isNonemptyFactor_iff_isFactor_and_ne_nil _ _).2
    ⟨by decide, (InfiniteWord.isFactor_iff_exists_factorList _ _).2 ⟨2, by decide⟩⟩
