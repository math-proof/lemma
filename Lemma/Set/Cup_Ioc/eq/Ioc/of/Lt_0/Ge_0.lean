import Lemma.Set.Cup.eq.UnionCupS
import Lemma.Set.Cup_Ioc.eq.Ioc0.of.Ge_0
import Lemma.Set.Cup_Ioc.eq.Ioc_0.of.Lt_0
open Set


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℤ}
-- given
  (h_a : a < 0)
  (h_b : b ≥ 0) :
-- imply
  ⋃ k ∈ Ico a b, Ioc (k : R) (k + 1 : R) = Ioc (a : R) (b : R) := by
-- proof
  set f : ℤ → Set R := fun k => Ioc (k : R) (k + 1 : R)
  if hb : b = 0 then
    subst hb
    simpa [f] using Cup_Ioc.eq.Ioc_0.of.Lt_0 (R := R) h_a
  else
    have hb_pos : 0 < b := lt_of_le_of_ne h_b (Ne.symm hb)
    rw [Cup.eq.UnionCupS f (Ico a b) (Ico a 0)]
    have h_inter : Ico a b ∩ Ico a 0 = Ico a 0 := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_Ico]
      constructor
      · rintro ⟨⟨ha, _⟩, hk0⟩
        exact hk0
      · intro ⟨ha, hk0⟩
        exact ⟨⟨ha, lt_trans hk0 hb_pos⟩, ⟨ha, hk0⟩⟩
    have h_sdiff : Ico a b \ Ico a 0 = Ico 0 b := by
      ext k
      simp only [Set.mem_sdiff, Set.mem_Ico]
      constructor
      · rintro ⟨⟨ha, hb'⟩, hnot⟩
        refine ⟨?_, hb'⟩
        by_contra hk
        push Not at hk
        exact hnot ⟨ha, hk⟩
      · rintro ⟨hk0, hb'⟩
        refine ⟨⟨?_, hb'⟩, ?_⟩
        · exact le_trans (le_of_lt h_a) hk0
        · intro ⟨ha, hk⟩
          exact not_lt.mpr hk0 hk
    rw [h_inter, h_sdiff]
    rw [Cup_Ioc.eq.Ioc_0.of.Lt_0 (R := R) h_a, Cup_Ioc.eq.Ioc0.of.Ge_0 (R := R) (le_of_lt hb_pos)]
    exact UnionIocS.eq.Ioc.of.Le.Le (by exact_mod_cast h_a.le) (by exact_mod_cast hb_pos.le)


-- created on 2018-10-13
-- updated on 2026-08-07
