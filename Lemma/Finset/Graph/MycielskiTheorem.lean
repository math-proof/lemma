import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Graph.MycielskiTheorem.Part4
open scoped SimpleGraph
open MetaMathlibExt


namespace MetaMathlibExt

/--
[myAdj_of01](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_of01 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
  myAdj G (some (v, false)) (some (u, true)) :=
  Or.inr (Or.inl ⟨v, u, rfl, rfl, h⟩)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_of10](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_of10 {V : Type*} {G : SimpleGraph V} {v u : V} (h : G.Adj v u) :
  myAdj G (some (v, true)) (some (u, false)) :=
  Or.inr (Or.inr (Or.inl ⟨v, u, rfl, rfl, h⟩))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_sh_ad](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_sh_ad {V : Type*} {G : SimpleGraph V} (v : V) :
  myAdj G (some (v, true)) none :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨v, rfl, rfl⟩)))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_ad_sh](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_ad_sh {V : Type*} {G : SimpleGraph V} (v : V) :
  myAdj G none (some (v, true)) :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨v, rfl, rfl⟩)))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_apex_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_apex_left {V : Type*} {G : SimpleGraph V} {y : Option (V × Bool)}
  (h : myAdj G none y) : ∃ v, y = some (v, true) := by
  simp only [myAdj] at h
  obtain ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | := h
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · cases ha
  · cases ha
  · cases ha
  · cases ha
  · exact ⟨a, hb⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_apex_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_apex_right {V : Type*} {G : SimpleGraph V} {x : Option (V × Bool)}
  (h : myAdj G x none) : ∃ v, x = some (v, true) := by
  simp only [myAdj] at h
  obtain ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | := h
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · cases hb
  · cases hb
  · cases hb
  · exact ⟨a, ha⟩
  · cases hb

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_to_G](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_to_G {V : Type*} {G : SimpleGraph V} {v u : V} {i j : Bool}
  (h : myAdj G (some (v, i)) (some (u, j))) : G.Adj v u := by
  simp only [myAdj] at h
  obtain ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | := h
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · have e1 : (v, i) = (a, false) := Option.some_inj.mp ha
    have e2 : (u, j) = (b, false) := Option.some_inj.mp hb
    have h1 : v = a := congrArg Prod.fst e1
    have h2 : u = b := congrArg Prod.fst e2
    rwa [h1, h2]
  · have e1 : (v, i) = (a, false) := Option.some_inj.mp ha
    have e2 : (u, j) = (b, true) := Option.some_inj.mp hb
    have h1 : v = a := congrArg Prod.fst e1
    have h2 : u = b := congrArg Prod.fst e2
    rwa [h1, h2]
  · have e1 : (v, i) = (a, true) := Option.some_inj.mp ha
    have e2 : (u, j) = (b, false) := Option.some_inj.mp hb
    have h1 : v = a := congrArg Prod.fst e1
    have h2 : u = b := congrArg Prod.fst e2
    rwa [h1, h2]
  · exact (Option.some_ne_none _ hb).elim
  · exact (Option.some_ne_none _ ha).elim

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myAdj_no_ss](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myAdj_no_ss {V : Type*} {G : SimpleGraph V} {v u : V}
  (h : myAdj G (some (v, true)) (some (u, true))) : False := by
  simp only [myAdj] at h
  obtain ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | ⟨a, b, ha, hb, hadj⟩ | := h
    ⟨a, ha, hb⟩ | ⟨a, ha, hb⟩
  · have e : (v, true) = (a, false) := Option.some_inj.mp ha
    have e2 : (true : Bool) = false := congrArg Prod.snd e
    cases e2
  · have e : (v, true) = (a, false) := Option.some_inj.mp ha
    have e2 : (true : Bool) = false := congrArg Prod.snd e
    cases e2
  · have e : (u, true) = (b, false) := Option.some_inj.mp hb
    have e2 : (true : Bool) = false := congrArg Prod.snd e
    cases e2
  · exact (Option.some_ne_none _ hb).elim
  · exact (Option.some_ne_none _ ha).elim

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myDesome](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myDesome {V : Type*} {x : Option (V × Bool)} (hx : x ≠ none) :
  ∃ v i, x = some (v, i) := by
  cases x with
  | none => exact (hx rfl).elim
  | some p =>
    obtain ⟨v, i⟩ := p
    exact ⟨v, i, rfl⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[completeGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma completeGraph_adj_iff {α : Type*} {x y : α} :
  (SimpleGraph.completeGraph α).Adj x y ↔ x ≠ y := by
  rw [SimpleGraph.completeGraph_eq_top]
  exact SimpleGraph.top_adj _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myRawColor_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myRawColor_ne {V : Type*} {k : ℕ} (d : Option (V × Bool) → Fin (k + 1))
  (j : Fin (k + 1)) (hd : ∀ v : V, d (some (v, true)) ≠ j) (v : V) :
  myRawColor d j v ≠ j := by
  unfold myRawColor
  split_ifs with h
  · exact hd v
  · exact h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myColorable_up](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myColorable_up {V : Type*} (G : SimpleGraph V) {m : ℕ}
  (c : G.Coloring (Fin m)) : (myGraph G).Colorable (m + 1) := by
  have hcprop : ∀ {v u : V}, G.Adj v u → c v ≠ c u := by
    intro v u h
    have h2 := c.map_rel' h
    rwa [completeGraph_adj_iff] at h2
  refine ⟨⟨fun x => match x with | some (v, _) => Fin.castSucc (c v) | none => Fin.last m, ?_⟩⟩
  intro x y hxy
  have hxy' : myAdj G x y := hxy
  rw [completeGraph_adj_iff]
  simp only [myAdj] at hxy'
  obtain ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ | ⟨v, u, rfl, rfl, h⟩ | := hxy'
    ⟨v, rfl, rfl⟩ | ⟨v, rfl, rfl⟩
  · dsimp only
    exact mt Fin.castSucc_inj.mp (hcprop h)
  · dsimp only
    exact mt Fin.castSucc_inj.mp (hcprop h)
  · dsimp only
    exact mt Fin.castSucc_inj.mp (hcprop h)
  · dsimp only
    exact Fin.castSucc_ne_last _
  · dsimp only
    exact Ne.symm (Fin.castSucc_ne_last _)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[myCliqueFree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma myCliqueFree {V : Type*} (G : SimpleGraph V)
  (hG : G.CliqueFree 3) : (myGraph G).CliqueFree 3 := by
  have hdec := Classical.decEq V
  intro s hs
  obtain ⟨hclique, hcard⟩ := hs
  obtain ⟨a, b, c, habne, hacne, hbcne, rfl⟩ := Finset.card_eq_three.mp hcard
  have ha_mem : a ∈ (↑({a, b, c} : Finset (Option (V × Bool))) : Set _) :=
    Finset.mem_coe.mpr (Finset.mem_insert_self a {b, c})
  have hb_mem : b ∈ (↑({a, b, c} : Finset (Option (V × Bool))) : Set _) :=
    Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_insert_self b {c}))
  have hc_mem : c ∈ (↑({a, b, c} : Finset (Option (V × Bool))) : Set _) :=
    Finset.mem_coe.mpr
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self c)))
  have hab : myAdj G a b := hclique ha_mem hb_mem habne
  have hac : myAdj G a c := hclique ha_mem hc_mem hacne
  have hbc : myAdj G b c := hclique hb_mem hc_mem hbcne
  have hane : a ≠ none := by
    intro h
    subst h
    obtain ⟨vb, rfl⟩ := myAdj_apex_left hab
    obtain ⟨vc, rfl⟩ := myAdj_apex_left hac
    exact myAdj_no_ss hbc
  have hbne : b ≠ none := by
    intro h
    subst h
    obtain ⟨va, rfl⟩ := myAdj_apex_right hab
    obtain ⟨vc, rfl⟩ := myAdj_apex_left hbc
    exact myAdj_no_ss hac
  have hcne : c ≠ none := by
    intro h
    subst h
    obtain ⟨va, rfl⟩ := myAdj_apex_right hac
    obtain ⟨vb, rfl⟩ := myAdj_apex_right hbc
    exact myAdj_no_ss hab
  obtain ⟨va, ia, rfl⟩ := myDesome hane
  obtain ⟨vb, ib, rfl⟩ := myDesome hbne
  obtain ⟨vc, ic, rfl⟩ := myDesome hcne
  have gab : G.Adj va vb := myAdj_to_G hab
  have gac : G.Adj va vc := myAdj_to_G hac
  have gbc : G.Adj vb vc := myAdj_to_G hbc
  have hvv01 : va ≠ vb := fun h => G.loopless.irrefl _ (h ▸ gab)
  have hvv02 : va ≠ vc := fun h => G.loopless.irrefl _ (h ▸ gac)
  have hvv12 : vb ≠ vc := fun h => G.loopless.irrefl _ (h ▸ gbc)
  have hcliqueG : G.IsClique (↑({va, vb, vc} : Finset V) : Set V) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx hy
    obtain rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl := hx
    · exact (hxy rfl).elim
    · exact gab
    · exact gac
    · exact G.symm.symm _ _ gab
    · exact (hxy rfl).elim
    · exact gbc
    · exact G.symm.symm _ _ gac
    · exact G.symm.symm _ _ gbc
    · exact (hxy rfl).elim
  have hcardG : ({va, vb, vc} : Finset V).card = 3 :=
    Finset.card_eq_three.mpr ⟨va, vb, vc, hvv01, hvv02, hvv12, rfl⟩
  exact hG {va, vb, vc} ⟨hcliqueG, hcardG⟩

end MetaMathlibExt

/--
[mycielski_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean)
-/
@[path]
private lemma mycielski_theorem_eq
  :
-- imply
  (∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
    G ⊑ H ∧
    Fintype.card V < Fintype.card W ∧
    (G.CliqueFree 3 → H.CliqueFree 3) ∧
    (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1)) ∧
    ∀ (k : ℕ), ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
    H.CliqueFree 3 ∧ (↑k ≤ H.chromaticNumber) := by
-- proof
  apply MetaMathlibExt.mycielski_theorem


-- created on 2026-10-20
-- updated on 2026-10-26
