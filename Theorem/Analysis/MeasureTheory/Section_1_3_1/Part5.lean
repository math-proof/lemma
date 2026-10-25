import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part5


namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- The atom index is bounded by 2^(k+k') -/
lemma atomIndexOf_lt {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) :
    atomIndexOf E E' x < 2^(k+k') := by
  unfold atomIndexOf
  have hpart1 : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) < 2^k :=
    sum_pow_two_fin_lt
  have hpart2_inner : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) < 2^k' :=
    sum_pow_two_fin_lt
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]
    congr 1; ext j'; rw [pow_add]
  rw [hrw]
  have h2k_pos : 0 < 2^k := Nat.two_pow_pos k
  have hpart2 : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) < 2^(k+k') := by
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
        < 2^k * 2^k' := (Nat.mul_lt_mul_left h2k_pos).mpr hpart2_inner
      _ = 2^(k+k') := by rw [← pow_add]
  -- Use tight bounds: sum1 ≤ 2^k - 1, sum2 ≤ 2^k * (2^k' - 1) = 2^(k+k') - 2^k
  -- So sum1 + sum2 ≤ (2^k - 1) + (2^(k+k') - 2^k) = 2^(k+k') - 1 < 2^(k+k')
  have hpart1_le : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) ≤ 2^k - 1 :=
    Nat.le_sub_one_of_lt hpart1
  have hpart2_le : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) ≤ 2^(k+k') - 2^k := by
    have inner_le : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) ≤ 2^k' - 1 :=
      Nat.le_sub_one_of_lt hpart2_inner
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
        ≤ 2^k * (2^k' - 1) := Nat.mul_le_mul_left _ inner_le
      _ = 2^k * 2^k' - 2^k := by rw [Nat.mul_sub_one]
      _ = 2^(k+k') - 2^k := by rw [pow_add]
  have h2k_le : 2^k ≤ 2^(k+k') := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k k')
  calc (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) +
       2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
      ≤ (2^k - 1) + (2^(k+k') - 2^k) := Nat.add_le_add hpart1_le hpart2_le
    _ = 2^(k+k') - 1 := by omega
    _ < 2^(k+k') := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)

/-- The atom index has bit j set iff x ∈ E j -/
lemma atomIndexOf_testBit_E {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k) :
    (atomIndexOf E E' x).testBit j.val ↔ x ∈ E j := by
  unfold atomIndexOf
  -- atomIndexOf = Part1 + Part2 where Part2 = 2^k * (inner sum)
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Use testBit_two_pow_mul_add: for j.val < k and Part1 < 2^k, testBit j only looks at Part1
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2:ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt, if_pos j.isLt]
  -- Now show: Part1.testBit j.val ↔ x ∈ E j
  rw [Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The atom index has bit (k+j) set iff x ∈ E' j -/
lemma atomIndexOf_testBit_E' {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k') :
    (atomIndexOf E E' x).testBit (k + j.val) ↔ x ∈ E' j := by
  unfold atomIndexOf
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Use testBit_two_pow_mul_add: for k + j.val ≥ k and Part1 < 2^k
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2:ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt]
  have hge : ¬ (k + j.val < k) := by omega
  rw [if_neg hge]
  -- Now show: Part2_inner.testBit ((k + j.val) - k) ↔ x ∈ E' j
  have hsub : (k + j.val) - k = j.val := Nat.add_sub_cancel_left k j.val
  rw [hsub, Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Original set E\_i is the union of atoms where bit i is 1 -/
lemma set_eq_biUnion_atoms {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k) :
    E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    -- Construct the atom index from x's membership pattern
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · -- Show atomMembership k k' n i = true
      rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E E E' x i]
      exact hx
    · -- Show x ∈ atom E E' n
      simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.1 i).mp hn_bit

/-- Original set E'\_i is the union of atoms where bit (k+i) is 1 -/
lemma set_eq_biUnion_atoms' {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k') :
    E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E' E E' x i]
      exact hx
    · simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.2 i).mp hn_bit

/-- Atoms are measurable if the original sets are -/
lemma atom_measurable {d k k' : ℕ} {E : Fin k → Set (EuclideanSpace' d)} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (hE' : ∀ i, LebesgueMeasurable (E' i)) (n : Fin (2^(k+k'))) :
    LebesgueMeasurable (atom E E' n) := by
  -- The atom is an intersection of sets of the form E_i or (E_i)ᶜ
  -- Rewrite atom as intersection
  have hatom_eq : atom E E' n =
      (⋂ i : Fin k, if atomMembership k k' n i then E i else (E i)ᶜ) ∩
      (⋂ i : Fin k', if atomMembership k k' n (k + i) then E' i else (E' i)ᶜ) := by
    ext x
    simp only [atom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte]
          exact (h1 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h1 i).mpr hx)
      · intro i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte]
          exact (h2 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h2 i).mpr hx)
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        specialize h1 i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte] at h1
          exact ⟨fun _ => h1, fun _ => hbit⟩
        · simp only [hbit] at h1
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h1 hx).elim⟩
      · intro i
        specialize h2 i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte] at h2
          exact ⟨fun _ => h2, fun _ => hbit⟩
        · simp only [hbit] at h2
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h2 hx).elim⟩
  rw [hatom_eq]
  -- Now show the intersection is measurable
  -- Each component is E i or (E i)ᶜ, both measurable
  -- Finite intersection of measurable sets is measurable
  apply LebesgueMeasurable.inter
  · -- First part: ⋂ i : Fin k, ... (finite intersection of measurable sets)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n i
    · simp only [h]; exact hE i
    · simp only [h]; exact (hE i).complement
  · -- Second part: ⋂ i : Fin k', ... (finite intersection of measurable sets)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]; exact hE' i
    · simp only [h]; exact (hE' i).complement

/-- Indicator function evaluates to c if x ∈ E -/
lemma indicator_mul_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∈ E) : c * (EReal.indicator E x) = c := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h, EReal.coe_one, mul_one]

/-- Indicator function evaluates to 0 if x ∉ E -/
lemma indicator_mul_not_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∉ E) : c * (EReal.indicator E x) = 0 := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h, EReal.coe_zero, mul_zero]

end UnsignedSimpleFunction.IntegralWellDef
