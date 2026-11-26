import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {k : ℕ}
  {x : ℕ → Finset ℤ}
-- given
  (h : ((Finset.range k).biUnion x).card = ∑ i < k, (x i).card) :
-- imply
  ∀ i < k, ∀ j ∈ Finset.range k \ {i}, x i ∩ x j = ∅ := by
-- proof
  intro i hi j hj
  have hiR : i ∈ Finset.range k := Finset.mem_range.mpr hi
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
  by_contra hne
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finset.mem_inter] at ha
  have hs : (Finset.range k).biUnion x = x i ∪ ((Finset.range k).erase i).biUnion x := by
    conv_lhs => rw [← Finset.insert_erase hiR]
    rw [Finset.biUnion_insert]
  have hmem : a ∈ x i ∩ ((Finset.range k).erase i).biUnion x :=
    Finset.mem_inter.mpr ⟨ha.1, Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr ⟨hj.2, hj.1⟩, ha.2⟩⟩
  have h1 := Finset.card_union_add_card_inter (x i) (((Finset.range k).erase i).biUnion x)
  have h2 : 0 < (x i ∩ ((Finset.range k).erase i).biUnion x).card := Finset.card_pos.mpr ⟨a, hmem⟩
  have h3 := Finset.card_biUnion_le (s := (Finset.range k).erase i) (t := x)
  have h4 := Finset.add_sum_erase (Finset.range k) (fun i => (x i).card) hiR
  rw [hs, Nat.Iio_eq_range] at h
  omega


-- created on 2020-07-18
