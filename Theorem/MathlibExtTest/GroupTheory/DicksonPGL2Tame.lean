/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/DicksonPGL2Tame.lean -/


import Theorem.GroupTheory.DicksonPGL2Tame.Part4
import Lemma.Nat.Card_Stabilizer


namespace MathlibExtTest.GroupTheory.DicksonPGL2Tame

open MetaMathlibExt

-- A tame subgroup of prime order seven can only lie in the cyclic case.
example {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
    (G : Subgroup (Dickson.PGL p)) [Finite G]
    (hcard : Nat.card G = 7) (htame : ¬p ∣ Nat.card G) (hne : Nontrivial G) :
    IsCyclic G := by
  rcases Dickson.classification_tame p G htame hne with h | h
  · exact h
  rcases h with ⟨n, hn, ⟨e⟩⟩ | h
  · have hc := Nat.card_congr e.toEquiv
    rw [hcard, DihedralGroup.nat_card] at hc
    omega
  rcases h with ⟨⟨e⟩⟩ | h
  · have hc := Nat.card_congr e.toEquiv
    rw [hcard, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
    norm_num [Nat.factorial] at hc
  rcases h with ⟨⟨e⟩⟩ | h
  · have hc := Nat.card_congr e.toEquiv
    rw [hcard, Nat.card_perm, Nat.card_fin] at hc
    norm_num [Nat.factorial] at hc
  rcases h with ⟨e⟩
  · have hc := Nat.card_congr e.toEquiv
    rw [hcard, Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hc
    norm_num [Nat.factorial] at hc

end MathlibExtTest.GroupTheory.DicksonPGL2Tame
