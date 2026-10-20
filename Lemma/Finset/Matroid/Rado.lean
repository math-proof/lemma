import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Matroid.Rado
open MathlibExt.Combinatorics.Matroid.RadoWanted


/--
[rado_matroidal_marriage'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Rado.lean)
-/
@[path]
private lemma rado_matroidal_marriage'_eq
  [Finite I] [Finite E]
  {M : Matroid E}
  {A : I → Set E} :
-- imply
  (∃ f : I → E, Function.Injective f ∧ (∀ i, f i ∈ A i) ∧
    M.Indep (Set.range f)) ↔
    ∀ J : Finset I, (J.card : ℕ∞) ≤ M.eRk (⋃ i ∈ J, A i) := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.RadoWanted.rado_matroidal_marriage' A

/--
[rado_matroidal_marriage](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Rado.lean)
-/
@[path]
private lemma rado_matroidal_marriage_eq
  [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  {M : Matroid E}
  {A : I → Set E}
-- given
  (hM : M.E = Set.univ) :
-- imply
  (∃ f : I → E, Function.Injective f ∧ (∀ i, f i ∈ A i) ∧
    M.Indep (Set.range f)) ↔
    ∀ J : Finset I, (J.card : ℕ∞) ≤ M.eRk (⋃ i ∈ J, A i) := by
-- proof
  apply MathlibExt.Combinatorics.Matroid.RadoWanted.rado_matroidal_marriage hM A


-- created on 2026-10-20
