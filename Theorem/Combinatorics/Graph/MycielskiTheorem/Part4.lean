/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/MycielskiTheorem.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Algebra.CharP.Defs
import Mathlib.Order.CompletePartialOrder
import Def.Combinatorics.Graph.MycielskiTheorem.Part4


namespace MetaMathlibExt

open scoped SimpleGraph

theorem myStepU.{u_1, u_2} {V : Type u_1} [Fintype V] (G : SimpleGraph V) :
    ∃ (W : Type u_2) (_ : Fintype W) (H : SimpleGraph W),
      G ⊑ H ∧
        Fintype.card V < Fintype.card W ∧
          (G.CliqueFree 3 → H.CliqueFree 3) ∧
          (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1) := by
  have e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  obtain ⟨W0, hW0, H0, emb0, card0, free0, chrom0⟩ := myStep0 (mapGraph e G)
  have e2 : W0 ≃ ULift W0 := Equiv.ulift.symm
  refine ⟨ULift W0, inferInstance, mapGraph e2 H0, ?_, ?_, ?_, ?_⟩
  · exact SimpleGraph.IsContained.trans
      (SimpleGraph.IsContained.trans ⟨copyOfIso (isoMap e G)⟩ emb0) ⟨copyOfIso (isoMap e2 H0)⟩
  · have hc1 : Fintype.card V = Fintype.card (Fin (Fintype.card V)) := Fintype.card_congr e
    have hc2 : Fintype.card W0 = Fintype.card (ULift W0) := Fintype.card_congr e2
    omega
  · intro hG
    have hG0 : (mapGraph e G).CliqueFree 3 :=
      SimpleGraph.CliqueFree.comap ⟨copyOfIso (isoMap e G).symm⟩ hG
    exact SimpleGraph.CliqueFree.comap ⟨copyOfIso (isoMap e2 H0).symm⟩ (free0 hG0)
  · intro hGne
    have chromG0 : (mapGraph e G).chromaticNumber = G.chromaticNumber :=
      (SimpleGraph.chromaticNumber_congr (isoMap e G)).symm
    have hG0ne : (mapGraph e G).chromaticNumber ≠ ⊤ := by
      rw [chromG0]
      exact hGne
    have chromH : (mapGraph e2 H0).chromaticNumber = H0.chromaticNumber :=
      (SimpleGraph.chromaticNumber_congr (isoMap e2 H0)).symm
    rw [chromH, chrom0 hG0ne, chromG0]

theorem myKey.{u} (n : ℕ) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      H.CliqueFree 3 ∧ H.chromaticNumber = ↑n := by
  induction n with
  | zero =>
    refine ⟨ULift Empty, inferInstance, ⊥, ?_, ?_⟩
    · apply SimpleGraph.cliqueFree_of_card_lt
      have hcc : Fintype.card (ULift Empty) = Fintype.card Empty := Fintype.card_congr Equiv.ulift
      rw [hcc, Fintype.card_empty]
      decide
    · simp
  | succ n ih =>
    obtain ⟨V, hV, G, hfree, hchi⟩ := ih
    obtain ⟨W, hW, H, _, _, hfreeH, hchiH⟩ := myStep0 G
    have hne : G.chromaticNumber ≠ ⊤ := by
      rw [hchi]
      exact ENat.natCast_ne_top n
    refine ⟨W, hW, H, hfreeH hfree, ?_⟩
    rw [hchiH hne, hchi, Nat.cast_add, Nat.cast_one]

/-- **Mycielski's theorem** (statement ID `mycielski-theorem-s1`; primary source:
J. Mycielski, "Sur le coloriage des graphes" (1955),
https://doi.org/10.4064/cm-3-2-161-162). We abstract the explicit Mycielski construction
to the existence of a larger finite graph `H` containing a copy of `G`. The resulting
graph is triangle-free whenever `G` is and has chromatic number one larger when the
chromatic number of `G` is finite. Consequently, there exist triangle-free graphs of
arbitrarily large chromatic number.

Proves `Wanted` entry `mycielski_theorem`.
-/
theorem mycielski_theorem :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
        G ⊑ H ∧
          Fintype.card V < Fintype.card W ∧
              (G.CliqueFree 3 → H.CliqueFree 3) ∧
                (G.chromaticNumber ≠ ⊤ → H.chromaticNumber = G.chromaticNumber + 1)) ∧
    ∀ (k : ℕ), ∃ (W : Type*) (_ : Fintype W) (H : SimpleGraph W),
      H.CliqueFree 3 ∧ (↑k ≤ H.chromaticNumber) := by
  constructor
  · intro V hV G
    exact myStepU G
  · intro k
    obtain ⟨W, hW, H, hfree, hchi⟩ := myKey k
    exact ⟨W, hW, H, hfree, hchi.ge⟩

end MetaMathlibExt
