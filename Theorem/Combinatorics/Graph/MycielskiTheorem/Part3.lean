/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Def.Combinatorics.Graph.MycielskiTheorem.Part3


namespace MetaMathlibExt

open scoped SimpleGraph

theorem myRawColor_ne_of_adj {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (d : Option (V × Bool) → Fin (k + 1)) (j : Fin (k + 1))
    (hdprop : ∀ {x y : Option (V × Bool)}, myAdj G x y → d x ≠ d y)
    {u v : V} (huv : G.Adj u v) :
    myRawColor d j u ≠ myRawColor d j v := by
  unfold myRawColor
  split_ifs with hu hv
  · exact False.elim ((hdprop (myAdj_of00 huv)) (hu.trans hv.symm))
  · exact hdprop (myAdj_of10 huv)
  · exact hdprop (myAdj_of01 huv)
  · exact hdprop (myAdj_of00 huv)

theorem myColorable_down {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (d : (myGraph G).Coloring (Fin (k + 1))) : G.Colorable k := by
  have hdprop : ∀ {x y : Option (V × Bool)}, myAdj G x y → d x ≠ d y := by
    intro x y h
    have h2 := d.map_rel' h
    rwa [completeGraph_adj_iff] at h2
  have hcard : Fintype.card ↥(Finset.univ.erase (d none)) = k := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fun v => e ⟨myRawColor (⇑d) (d none) v, ?_⟩, ?_⟩⟩
  · rw [Finset.mem_erase]
    exact ⟨myRawColor_ne (⇑d) (d none) (fun v => hdprop (myAdj_sh_ad v)) v, Finset.mem_univ _⟩
  · intro u v huv
    rw [completeGraph_adj_iff]
    intro hcon
    exact myRawColor_ne_of_adj (⇑d) (d none) hdprop huv (congrArg Subtype.val (e.injective hcon))

theorem myStep0.{u} {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      G ⊑ H ∧
        Fintype.card V < Fintype.card W ∧
          (G.CliqueFree 3 → H.CliqueFree 3) ∧
          (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1) := by
  refine ⟨Option (V × Bool), inferInstance, myGraph G, ⟨myCopy G⟩, ?_, ?_, ?_⟩
  · have hcard : Fintype.card (Option (V × Bool)) = Fintype.card V * 2 + 1 := by
      rw [Fintype.card_option, Fintype.card_prod, Fintype.card_bool]
    omega
  · exact myCliqueFree G
  · intro hGne
    have hm : G.chromaticNumber = ↑(G.chromaticNumber.toNat) := (ENat.natCast_toNat hGne).symm
    obtain ⟨c⟩ := SimpleGraph.colorable_of_chromaticNumber_ne_top hGne
    have hup : (myGraph G).chromaticNumber ≤ ↑(G.chromaticNumber.toNat + 1) :=
      (myColorable_up G c).chromaticNumber_le
    obtain ⟨d⟩ := SimpleGraph.colorable_chromaticNumber_of_fintype (myGraph G)
    have hHne : (myGraph G).chromaticNumber ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) SimpleGraph.chromaticNumber_le_card
    have ht0 : (myGraph G).chromaticNumber.toNat ≠ 0 := by
      intro hcon
      rw [hcon] at d
      exact Fin.elim0 (d none)
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_one_of_ne_zero ht0
    have dt : (myGraph G).Coloring (Fin (t + 1)) := by
      rw [← ht]
      exact d
    have hdown : G.Colorable t := myColorable_down G dt
    have hlow : G.chromaticNumber ≤ ↑t := hdown.chromaticNumber_le
    have hmt : G.chromaticNumber.toNat ≤ t := by
      rw [hm] at hlow
      exact Nat.cast_le.mp hlow
    have hfin : ((G.chromaticNumber.toNat + 1 : ℕ) : ℕ∞) ≤ ↑(t + 1) :=
      Nat.cast_le.mpr (Nat.succ_le_succ hmt)
    have hHcast : ((t + 1 : ℕ) : ℕ∞) = (myGraph G).chromaticNumber := by
      rw [← ht]
      exact ENat.natCast_toNat hHne
    have ecast : ((G.chromaticNumber.toNat + 1 : ℕ) : ℕ∞) = ↑G.chromaticNumber.toNat + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    have e2 : ((G.chromaticNumber.toNat + 1 : ℕ) : ℕ∞) ≤ (myGraph G).chromaticNumber := by
      rw [← hHcast]
      exact hfin
    rw [hm, ← ecast]
    exact le_antisymm hup e2

end MetaMathlibExt
