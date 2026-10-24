import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.SimpleGraph.EdgeGraceful
open EdgeGracefulTest


namespace EdgeGracefulTest

/--
[key2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
lemma key2
-- imply
  ∀ s : Sym2 (Fin 2), s ∈ (⊤ : SimpleGraph (Fin 2)).edgeSet → (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s :=
-- proof
  fun s hs => Sym2.ind (fun a b h => by
    have hadj : (⊤ : SimpleGraph (Fin 2)).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp h
    have hne : a ≠ b := (SimpleGraph.top_adj a b).mp hadj
    fin_cases a <;> fin_cases b
    · exact False.elim (hne rfl)
    · exact ⟨Sym2.mem_mk_left _ _, Sym2.mem_mk_right _ _⟩
    · exact ⟨Sym2.mem_mk_right _ _, Sym2.mem_mk_left _ _⟩
    · exact False.elim (hne rfl)) s hs

end EdgeGracefulTest

/--
[he01](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma he01_eq :
-- imply
  ((e01 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) = Sym2.mk (0 : Fin 3) 1 := by
-- proof
  apply EdgeGracefulTest.he01

/--
[he12](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma he12_eq :
-- imply
  ((e12 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) = Sym2.mk (1 : Fin 3) 2 := by
-- proof
  apply EdgeGracefulTest.he12

/--
[hto01](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma hto01_eq :
-- imply
  pathToFun e01 = 0 := by
-- proof
  apply EdgeGracefulTest.hto01

/--
[hto12](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma hto12_eq :
-- imply
  pathToFun e12 = 1 := by
-- proof
  apply EdgeGracefulTest.hto12

/--
[hinv0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma hinv0_eq :
-- imply
  pathInvFun 0 = e01 := by
-- proof
  apply EdgeGracefulTest.hinv0

/--
[hinv1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma hinv1_eq :
-- imply
  pathInvFun 1 = e12 := by
-- proof
  apply EdgeGracefulTest.hinv1

/--
[sclass](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma sclass_eq :
-- imply
  ∀ s : Sym2 (Fin 3), s ∈ (SimpleGraph.pathGraph 3).edgeSet → s = Sym2.mk (0 : Fin 3) 1 ∨ s = Sym2.mk (1 : Fin 3) 2 := by
-- proof
  apply EdgeGracefulTest.sclass

/--
[eclass](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean)
-/
@[path]
private lemma eclass_eq :
-- imply
  ∀ e : (SimpleGraph.pathGraph 3).edgeSet, e = e01 ∨ e = e12 := by
-- proof
  apply EdgeGracefulTest.eclass


-- created on 2026-10-23
