import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part10


namespace RealSimpleFunction.DisjointRepr

open UnsignedSimpleFunction.IntegralWellDef

/-- Single atoms are measurable -/
lemma singleAtom_measurable {d k : ℕ} {E : Fin k → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (n : Fin (2^k)) :
    LebesgueMeasurable (singleAtom E n) := by
  simp only [singleAtom]
  exact atom_measurable hE (fun i => Fin.elim0 i) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- On a point in singleAtom n, the original sum equals atomValue n -/
lemma sum_indicator_eq_atomValue {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d))
    (n : Fin (2^k)) (x : EuclideanSpace' d) (hx : x ∈ singleAtom E n) :
    (∑ i : Fin k, (c i) * (E i).indicator' x) = atomValue c n := by
  simp only [atomValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [mem_singleAtom_iff] at hx
  by_cases hbit : (n.val.testBit i.val) = true
  · simp only [hbit, ↓reduceIte]
    have hx_in : x ∈ E i := (hx i).mp hbit
    simp only [Set.indicator'_of_mem hx_in, mul_one]
  · have hbit_false : (n.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ E i := fun h => hbit ((hx i).mpr h)
    simp only [Set.indicator'_of_notMem hx_out, mul_zero, hbit_false, Bool.false_eq_true,
      ↓reduceIte]

/-- The original function equals the sum over atoms with atomValue coefficients -/
lemma eq_sum_atomValue_indicator {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d)) :
    (∑ i : Fin k, (c i) • (E i).indicator') = ∑ n : Fin (2^k), (atomValue c n) • (singleAtom E n).indicator' := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ⟨n, hn_mem, hn_unique⟩ := exists_unique_singleAtom E x
  have hrhs : (∑ m : Fin (2^k), atomValue c m * (singleAtom E m).indicator' x) = atomValue c n := by
    rw [Finset.sum_eq_single n]
    · simp only [Set.indicator'_of_mem hn_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ singleAtom E m := fun h => hm_ne (hn_unique m h)
      simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  rw [hrhs]
  exact sum_indicator_eq_atomValue c E n x hn_mem

end RealSimpleFunction.DisjointRepr

/-- Disjoint representation: any {name}`RealSimpleFunction` has an equivalent representation
    with pairwise disjoint, measurable sets. -/
lemma RealSimpleFunction.disjoint_representation {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) :
    ∃ (n:ℕ) (v: Fin n → ℝ) (A: Fin n → Set (EuclideanSpace' d)),
      (∀ i, LebesgueMeasurable (A i)) ∧
      Set.univ.PairwiseDisjoint A ∧
      f = ∑ i, (v i) • (A i).indicator' := by
  open UnsignedSimpleFunction.IntegralWellDef in
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use 2^k, UnsignedSimpleFunction.IntegralWellDef.atomValue c,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom E
  refine ⟨?_, ?_, ?_⟩
  · exact fun i => DisjointRepr.singleAtom_measurable hmes i
  · exact UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E
  · rw [heq]
    exact DisjointRepr.eq_sum_atomValue_indicator c E

