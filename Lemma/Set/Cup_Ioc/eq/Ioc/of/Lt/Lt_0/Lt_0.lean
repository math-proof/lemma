import Lemma.Set.Cup_UFn.of.Eq
import Lemma.Set.Cup.eq.UnionCupS
import Lemma.Set.Cup_Ioc.eq.Ioc_0.of.Lt_0
open Set


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  {a b : ℤ}
-- given
  (h_a : a < 0)
  (h_b : b < 0)
  (h_ab : a < b) :
-- imply
  ⋃ k ∈ Ico a b, Ioc (k : R) (k + 1 : R) = Ioc (a : R) (b : R) := by
-- proof
  set f : ℤ → Set R := fun k => Ioc (k : R) (k + 1 : R)
  simpa [f] using calc
    _ = ((⋃ k ∈ Ico a b, f k) ∪ Ioc (b : R) (0 : R)) \ Ioc (b : R) (0 : R) := by
      symm
      apply Set.union_sdiff_cancel_right
      apply subset_of_eq
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx, hxb⟩
      rw [In_Cup.is.Any_In.set] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      obtain ⟨hk1, hk2⟩ := hk
      have hk' : (k : R) + 1 ≤ (b : R) := by exact_mod_cast hk2
      grind
    _ = (Ioc (a : R) (b : R) ∪ Ioc (b : R) (0 : R)) \ Ioc (b : R) (0 : R) := by
      congr 1
      calc
        _ = (⋃ k ∈ Ico a b, f k) ∪ ⋃ k ∈ Ico b 0, f k := by
          congr 1
          simpa [f] using Ioc_0.eq.Cup_Ioc.of.Lt_0 h_b
        _ = Ioc (a : R) (b : R) ∪ Ioc (b : R) (0 : R) := calc
          _ = ⋃ k ∈ Ico a 0, f k := by
            rw [← Set.union_comm]
            rw [Cup.eq.UnionCupS f (Ico a 0) (Ico b 0)]
            congr 1 <;>
            .
              apply Cup_UFn.of.Eq
              grind
          _ = Ioc (a : R) (0 : R) := by simpa [f] using Cup_Ioc.eq.Ioc_0.of.Lt_0 h_a
          _ = Ioc (a : R) (b : R) ∪ Ioc (b : R) (0 : R) := Ioc.eq.UnionIocS.of.Le.Le (by exact_mod_cast h_ab.le) (by exact_mod_cast h_b.le)
    _ = Ioc (a : R) (b : R) := by grind


-- created on 2018-10-15
