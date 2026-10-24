import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Frucht
open MathlibExt.Combinatorics.SimpleGraph.FruchtWanted


namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

/--
[frucht_of_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean)
-/
@[path]
private lemma frucht_of_card_le_one {G : Type*} [Group G] [Fintype G]
  (h : Fintype.card G ≤ 1) :
  ∃ (n : ℕ) (Γ : SimpleGraph (Fin n)), Nonempty (G ≃* (Γ ≃g Γ)) := by
  refine ⟨1, ⊥, ?_⟩
  have hsubG : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp h
  have huniqG : Unique G := @uniqueOfSubsingleton G hsubG 1
  have hsubP : Subsingleton ((⊥ : SimpleGraph (Fin 1)) ≃g (⊥ : SimpleGraph (Fin 1))) := by
    constructor
    intro a b
    apply RelIso.ext
    intro x
    exact Subsingleton.elim _ _
  have huniqP : Unique ((⊥ : SimpleGraph (Fin 1)) ≃g (⊥ : SimpleGraph (Fin 1))) :=
    @uniqueOfSubsingleton _ hsubP 1
  refine ⟨?_⟩
  haveI := huniqG
  haveI := huniqP
  exact MulEquiv.ofUnique

end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

namespace MathlibExt.Combinatorics.SimpleGraph.FruchtWanted

/--
[frucht](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean)
-/
@[path]
lemma frucht
  [Group G] [Fintype G] [DecidableEq G] :
-- imply
  ∃ (n : ℕ) (Γ : SimpleGraph (Fin n)), Nonempty (G ≃* (Γ ≃g Γ)) := by
-- proof
  by_cases h : Fintype.card G ≤ 1
  · exact frucht_of_card_le_one h
  · have hN : 2 ≤ Fintype.card G := by omega
    let N := Fintype.card G
    let e : G ≃ Fin N := Fintype.equivFin G
    let V := G ⊕ (G × Fin N)
    let f : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
    refine ⟨Fintype.card V, (fruchtGraph N e).comap ⇑(f.symm), ?_⟩
    have h1 : G ≃* fruchtGraph N e ≃g fruchtGraph N e := fruchtMulEquiv N e hN
    have h2 : ((fruchtGraph N e).comap ⇑(f.symm)) ≃g ((fruchtGraph N e).comap ⇑(f.symm))
      ≃* fruchtGraph N e ≃g fruchtGraph N e :=
      graphAutComapEquiv (f.symm) (fruchtGraph N e)
    exact ⟨h1.trans h2.symm⟩
end MathlibExt.Combinatorics.SimpleGraph.FruchtWanted



-- created on 2026-10-20
-- updated on 2026-10-23
