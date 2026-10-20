import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.GeneralizedExtremal
open SimpleGraph


/--
[generalizedExtremalNumber_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma generalizedExtremalNumber_eq_sup_eq
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β} :
-- imply
  generalizedExtremalNumber n T H =
    Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
    (fun G => G.copyCount T) := by
-- proof
  apply SimpleGraph.generalizedExtremalNumber_eq_sup n T H

/--
[copyCount_le_generalizedExtremalNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma copyCount_le_generalizedExtremalNumber_eq
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β}
  {G : SimpleGraph (Fin n)}
-- given
  (hG : H.Free G) :
-- imply
  G.copyCount T ≤ generalizedExtremalNumber n T H := by
-- proof
  apply SimpleGraph.copyCount_le_generalizedExtremalNumber n T H G hG

/--
[generalizedExtremalNumber_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma generalizedExtremalNumber_le_iff_eq
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β}
  {m : ℕ} :
-- imply
  generalizedExtremalNumber n T H ≤ m ↔
    ∀ G : SimpleGraph (Fin n), H.Free G → G.copyCount T ≤ m := by
-- proof
  apply SimpleGraph.generalizedExtremalNumber_le_iff n T H m

/--
[exists_free_copyCount_eq_generalizedExtremalNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/GeneralizedExtremal.lean)
-/
@[path]
private lemma exists_free_copyCount_eq_generalizedExtremalNumber_eq
  [Fintype α]
  {n : ℕ}
  {T : SimpleGraph α}
  {H : SimpleGraph β}
-- given
  (hne : ∃ G : SimpleGraph (Fin n), H.Free G) :
-- imply
  ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.copyCount T = generalizedExtremalNumber n T H := by
-- proof
  apply SimpleGraph.exists_free_copyCount_eq_generalizedExtremalNumber n T H hne


-- created on 2026-10-20
