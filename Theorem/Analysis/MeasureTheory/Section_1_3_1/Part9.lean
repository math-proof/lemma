import Theorem.Analysis.MeasureTheory.Section_1_2_3.Part2
import Theorem.Analysis.Misc.NatBitwise
import Def.Analysis.MeasureTheory.Section_1_3_1.Part9


lemma UnsignedSimpleFunction.support_measurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : LebesgueMeasurable (Support f) := by
  -- Extract the representation: f = ∑ i, c(i) • EReal.indicator(E_i)
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf
  -- Define E' i = E i if c i > 0, else ∅
  let E' : Fin k → Set (EuclideanSpace' d) := fun i => if c i > 0 then E i else ∅
  -- Each E' i is measurable
  have hE'_meas : ∀ i, LebesgueMeasurable (E' i) := fun i => by
    simp only [E']
    split_ifs with h
    · exact (hmes_nonneg i).1
    · exact LebesgueMeasurable.empty
  -- Key: Support f = ⋃ i, E' i
  have h_eq : Support f = ⋃ i, E' i := by
    ext x
    simp only [Support, Set.mem_setOf_eq, Set.mem_iUnion, E']
    constructor
    · -- (⊆) If f(x) ≠ 0, some c_i > 0 and x ∈ E_i
      intro hne
      rw [heq] at hne
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hne
      -- Sum of nonneg terms is nonzero, so some term is nonzero
      have h_exists := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨i, _, hi_ne⟩ := h_exists
      use i
      -- c i * indicator ≠ 0 means c i > 0 and x ∈ E i
      by_cases hc : c i > 0
      · simp only [hc, ↓reduceIte]
        by_cases hx : x ∈ E i
        · exact hx
        · -- If x ∉ E i, then indicator is 0, so c i * 0 = 0, contradiction
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx,
                     EReal.coe_zero, mul_zero] at hi_ne
          exact absurd rfl hi_ne
      · -- c i ≤ 0, but c i ≥ 0, so c i = 0
        have hc_zero : c i = 0 := le_antisymm (le_of_not_gt hc) (hmes_nonneg i).2
        simp only [hc_zero, zero_mul] at hi_ne
        exact absurd rfl hi_ne
    · -- (⊇) If x ∈ E' i for some i, then f(x) ≠ 0
      intro ⟨i, hi⟩
      split_ifs at hi with hc
      · -- c i > 0 and x ∈ E i
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        -- f(x) ≥ c i * indicator(E i)(x) = c i > 0
        have h_term_pos : c i * EReal.indicator (E i) x > 0 := by
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hi,
                     EReal.coe_one, mul_one]
          exact hc
        -- Sum of nonneg terms with one positive term is positive
        have h_sum_nonneg : ∀ j, 0 ≤ c j * EReal.indicator (E j) x := fun j =>
          mul_nonneg (hmes_nonneg j).2 (EReal.indicator_nonneg' (E j) x)
        have h_sum_pos : 0 < ∑ j : Fin k, c j * EReal.indicator (E j) x := by
          calc 0 < c i * EReal.indicator (E i) x := h_term_pos
            _ ≤ ∑ j : Fin k, c j * EReal.indicator (E j) x :=
                Finset.single_le_sum (fun j _ => h_sum_nonneg j) (Finset.mem_univ i)
        exact ne_of_gt h_sum_pos
      · -- hi : x ∈ ∅, contradiction
        exact absurd hi (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hE'_meas

lemma AlmostAlways.ofAlways {d:ℕ} {P: EuclideanSpace' d → Prop} (h: ∀ x, P x) : AlmostAlways P := by
  -- AlmostAlways P means IsNull { x | ¬ P x }, i.e., Lebesgue_outer_measure { x | ¬ P x } = 0
  -- If ∀ x, P x, then { x | ¬ P x } = ∅
  unfold AlmostAlways IsNull
  have h_empty : { x | ¬ P x } = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact h x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

lemma AlmostAlways.mp {d:ℕ} {P Q: EuclideanSpace' d → Prop} (hP: AlmostAlways P) (himp: ∀ x, P x → Q x) : AlmostAlways Q := by
  -- AlmostAlways P means IsNull { x | ¬ P x }, i.e., Lebesgue_outer_measure { x | ¬ P x } = 0
  -- If P → Q everywhere, then ¬Q → ¬P (contrapositive), so { x | ¬ Q x } ⊆ { x | ¬ P x }
  unfold AlmostAlways IsNull at *
  -- hP : Lebesgue_outer_measure { x | ¬ P x } = 0
  -- Goal: Lebesgue_outer_measure { x | ¬ Q x } = 0
  have h_subset : { x | ¬ Q x } ⊆ { x | ¬ P x } := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    exact fun hp => hx (himp x hp)
  -- By monotonicity: measure { x | ¬ Q x } ≤ measure { x | ¬ P x } = 0
  have h_le := Lebesgue_outer_measure.mono h_subset
  rw [hP] at h_le
  exact le_antisymm h_le (Lebesgue_outer_measure.nonneg _)

lemma AlmostAlways.countable {d:ℕ} {I: Type*} [Countable I] {P: I → EuclideanSpace' d → Prop} (hP: ∀ i, AlmostAlways (P i)) : AlmostAlways (fun x ↦ ∀ i, P i x) := by
  -- AlmostAlways (fun x ↦ ∀ i, P i x) means IsNull { x | ¬ ∀ i, P i x }
  -- { x | ¬ ∀ i, P i x } = { x | ∃ i, ¬ P i x } = ⋃ᵢ { x | ¬ P i x }
  -- Each { x | ¬ P i x } is null by hP, and a countable union of null sets is null
  unfold AlmostAlways IsNull at *
  -- Goal: Lebesgue_outer_measure { x | ¬ ∀ i, P i x } = 0
  -- hP i : Lebesgue_outer_measure { x | ¬ P i x } = 0
  have h_eq : { x | ¬ ∀ i, P i x } = ⋃ i, { x | ¬ P i x } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
  rw [h_eq]
  -- Need: Lebesgue_outer_measure (⋃ i, { x | ¬ P i x }) = 0
  -- Use countable type I via Encodable
  cases nonempty_encodable I with
  | intro enc =>
    -- Now have Encodable I, can use ℕ-indexed union
    -- Reindex via Encodable.encode
    let E' : ℕ → Set (EuclideanSpace' d) := fun n => match @Encodable.decode I enc n with
      | some i => { x | ¬ P i x }
      | none => ∅
    have h_subset : (⋃ i : I, { x | ¬ P i x }) ⊆ ⋃ n : ℕ, E' n := by
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      use @Encodable.encode I enc i
      simp only [E', @Encodable.encodek I enc]
      exact hi
    have h_le := Lebesgue_outer_measure.mono h_subset
    have h_E'_null : ∀ n, Lebesgue_outer_measure (E' n) = 0 := fun n => by
      simp only [E']
      cases h : @Encodable.decode I enc n with
      | none => exact Lebesgue_outer_measure.of_empty d
      | some i => exact hP i
    -- By countable subadditivity: m(⋃ E'_n) ≤ ∑' n, m(E'_n) = ∑' n, 0 = 0
    have h_sum_zero : ∑' n, Lebesgue_outer_measure (E' n) = 0 := by
      simp only [h_E'_null, tsum_zero]
    have h_union_le := Lebesgue_outer_measure.union_le E'
    have h_bound : Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x }) ≤ 0 :=
      calc Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x })
          ≤ Lebesgue_outer_measure (⋃ n, E' n) := h_le
        _ ≤ ∑' n, Lebesgue_outer_measure (E' n) := h_union_le
        _ = 0 := h_sum_zero
    exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Almost everywhere equality is reflexive -/
lemma AlmostEverywhereEqual.refl {d:ℕ} {X: Type*} (f: EuclideanSpace' d → X) :
    AlmostEverywhereEqual f f :=
  -- {x | f x ≠ f x} = ∅, which is null
  AlmostAlways.ofAlways (fun _ => rfl)

/-- Almost everywhere equality is symmetric -/
lemma AlmostEverywhereEqual.symm {d:ℕ} {X: Type*} {f g: EuclideanSpace' d → X}
    (h: AlmostEverywhereEqual f g) : AlmostEverywhereEqual g f := by
  -- {x | g x ≠ f x} = {x | f x ≠ g x}, same set
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  convert h using 2
  ext x
  exact ne_comm

/-- Almost everywhere equality is transitive -/
lemma AlmostEverywhereEqual.trans {d:ℕ} {X: Type*} {f g h: EuclideanSpace' d → X}
    (hfg: AlmostEverywhereEqual f g) (hgh: AlmostEverywhereEqual g h) :
    AlmostEverywhereEqual f h := by
  -- {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x}
  -- Union of two null sets is null
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  have h_subset : {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra hc
    push_neg at hc
    exact hx (hc.1.trans hc.2)
  -- Express union as ℕ-indexed union for countable subadditivity
  let E : ℕ → Set (EuclideanSpace' d) := fun n =>
    match n with
    | 0 => {x | f x ≠ g x}
    | 1 => {x | g x ≠ h x}
    | _ => ∅
  have h_union_eq : {x | f x ≠ g x} ∪ {x | g x ≠ h x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, E]
    constructor
    · intro hx
      cases hx with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      match n with
      | 0 => exact Or.inl hn
      | 1 => exact Or.inr hn
      | n + 2 => exact absurd hn (Set.notMem_empty x)
  have h_E_null : ∀ n, Lebesgue_outer_measure (E n) = 0 := fun n => by
    match n with
    | 0 => exact hfg
    | 1 => exact hgh
    | n + 2 => exact Lebesgue_outer_measure.of_empty d
  have h_sum_zero : ∑' n, Lebesgue_outer_measure (E n) = 0 := by simp only [h_E_null, tsum_zero]
  have h_union_le := Lebesgue_outer_measure.union_le E
  have h_bound : Lebesgue_outer_measure {x | f x ≠ h x} ≤ 0 :=
    calc Lebesgue_outer_measure {x | f x ≠ h x}
        ≤ Lebesgue_outer_measure (⋃ n, E n) := by rw [← h_union_eq]; exact Lebesgue_outer_measure.mono h_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_union_le
      _ = 0 := h_sum_zero
  exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Almost everywhere equality is an equivalence relation -/
theorem AlmostEverywhereEqual.equivalence {d:ℕ} {X: Type*} :
    Equivalence (@AlmostEverywhereEqual d X) :=
  ⟨refl, symm, trans⟩

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure, indicator) -/
lemma UnsignedSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') := by
  use 1, fun _ => (1 : EReal), fun _ => E
  constructor
  · intro
    exact ⟨hE, zero_le_one⟩
  · ext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_one]
    simp [EReal.indicator, Real.EReal_fun]

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure, integral of an indicator) -/
lemma UnsignedSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  (UnsignedSimpleFunction.indicator hE).integ = Lebesgue_measure E := by
  have hrep : Real.toEReal ∘ E.indicator' =
      ∑ i : Fin 1, (1 : EReal) • EReal.indicator ((fun _ : Fin 1 => E) i) := by
    ext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_one]
    simp [EReal.indicator, Real.EReal_fun]
  have h := integral_eq (indicator hE) (fun _ => hE) (fun _ => zero_le_one) hrep
  simpa [Fin.sum_univ_one] using h

