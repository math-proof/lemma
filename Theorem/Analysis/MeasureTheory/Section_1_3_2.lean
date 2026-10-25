import Theorem.Analysis.MeasureTheory.Section_1_3_1.Part11
import Mathlib.Algebra.Order.Floor.Semifield
import Abbrev.Analysis.MeasureTheory.Section_1_3_2
set_option doc.verso.suggestions false


namespace UnsignedMeasurable.TFAE_helpers

variable {d : ℕ} {f : EuclideanSpace' d → EReal}

/-! # (i) ⟺ (ii): By definition of {name}`UnsignedMeasurable` -/

private lemma i_iff_ii (hf : Unsigned f) : stmt_i f ↔ stmt_ii f := by
  simp only [UnsignedMeasurable]
  constructor
  · intro ⟨_, g, hg_simple, hg_conv⟩
    exact ⟨g, hg_simple, hg_conv⟩
  · intro ⟨g, hg_simple, hg_conv⟩
    exact ⟨hf, g, hg_simple, hg_conv⟩

/-! # (ii) ⟹ (iii): Pointwise everywhere implies pointwise a.e. -/

private lemma ii_imp_iii : stmt_ii f → stmt_iii f := by
  intro ⟨g, hg_simple, hg_conv⟩
  refine ⟨g, hg_simple, ?_⟩
  -- AlmostAlways P means IsNull {x | ¬P x}
  -- Since pointwise convergence holds everywhere, {x | ¬Tendsto} = ∅
  simp only [PointwiseAeConvergesTo, AlmostAlways]
  have h_empty : {x | ¬Filter.atTop.Tendsto (fun n ↦ g n x) (nhds (f x))} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hg_conv x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

/-! # (iv) ⟹ (ii): Monotone sequences in \[0,∞\] converge to their supremum -/

private lemma iv_imp_ii : stmt_iv f → stmt_ii f := by
  intro ⟨g, hg_props, hg_mono, hg_sup⟩
  refine ⟨g, fun n => (hg_props n).1, ?_⟩
  intro x
  rw [hg_sup x]
  -- For monotone sequences in EReal, g n x → iSup (g · x)
  exact tendsto_atTop_iSup (hg_mono x)

/-! # (iii) ⟹ (v): Via limsup representation -/

-- Helper: Set.indicator' equals 1 when x ∈ E
private lemma Set.indicator'_eq_one' {X : Type*} {E : Set X} {x : X} (hx : x ∈ E) :
    ((E.indicator' x : ℝ) : EReal) = 1 := by
  classical
  rw [Set.indicator'_apply, if_pos hx]
  rfl

-- Helper: Set.indicator' equals 0 when x ∉ E
private lemma Set.indicator'_eq_zero' {X : Type*} {E : Set X} {x : X} (hx : x ∉ E) :
    ((E.indicator' x : ℝ) : EReal) = 0 := by
  classical
  rw [Set.indicator'_apply, if_neg hx]
  rfl

-- Level sets of simple functions are Lebesgue measurable
private lemma UnsignedSimpleFunction.levelset_gt_LebesgueMeasurable
    {g : EuclideanSpace' d → EReal} (hg : UnsignedSimpleFunction g) (t : EReal) :
    LebesgueMeasurable {x | g x > t} := by
  obtain ⟨k, c, E, hE_props, heq⟩ := hg
  -- For each subset S of Fin k, define the "atom" R_S where x ∈ E_i iff i ∈ S
  let R : Finset (Fin k) → Set (EuclideanSpace' d) :=
    fun S => (⋂ i ∈ S, E i) ∩ (⋂ i ∈ Sᶜ, (E i)ᶜ)
  -- Each R_S is measurable
  have hR_meas : ∀ S, LebesgueMeasurable (R S) := by
    intro S
    apply LebesgueMeasurable.inter
    · apply LebesgueMeasurable.finset_inter; intro i _; exact (hE_props i).1
    · apply LebesgueMeasurable.finset_inter; intro i _; exact (hE_props i).1.complement
  -- On R_S, g is constant with value ∑_{i ∈ S} c_i
  have hg_const : ∀ S x, x ∈ R S → g x = ∑ i ∈ S, c i := by
    intro S x hx
    rw [heq]
    simp only [Finset.sum_apply, Pi.smul_apply]
    have h_split : ∑ i : Fin k, c i • EReal.indicator (E i) x =
                   ∑ i ∈ S, c i • EReal.indicator (E i) x +
                   ∑ i ∈ Sᶜ, c i • EReal.indicator (E i) x := by
      rw [← Finset.sum_add_sum_compl S]
    rw [h_split]
    simp only [R, Set.mem_inter_iff, Set.mem_iInter] at hx
    obtain ⟨hx_in, hx_out⟩ := hx
    have h_in : ∀ i ∈ S, EReal.indicator (E i) x = 1 := by
      intro i hi; have hxi : x ∈ E i := hx_in i hi
      simp only [EReal.indicator, Real.EReal_fun]; exact Set.indicator'_eq_one' hxi
    have h_out : ∀ i ∈ Sᶜ, EReal.indicator (E i) x = 0 := by
      intro i hi; have hxi : x ∉ E i := hx_out i hi
      simp only [EReal.indicator, Real.EReal_fun]; exact Set.indicator'_eq_zero' hxi
    calc ∑ i ∈ S, c i • EReal.indicator (E i) x + ∑ i ∈ Sᶜ, c i • EReal.indicator (E i) x
        = ∑ i ∈ S, c i • (1 : EReal) + ∑ i ∈ Sᶜ, c i • (0 : EReal) := by
          congr 1
          · exact Finset.sum_congr rfl (fun i hi => by rw [h_in i hi])
          · exact Finset.sum_congr rfl (fun i hi => by rw [h_out i hi])
      _ = ∑ i ∈ S, c i + 0 := by simp [smul_eq_mul]
      _ = ∑ i ∈ S, c i := add_zero _
  -- Every x belongs to exactly one R_S
  have h_partition : ∀ x, ∃! S, x ∈ R S := by
    intro x
    have hDec : DecidablePred (fun i => x ∈ E i) := Classical.decPred _
    let S := (Finset.univ : Finset (Fin k)).filter (fun i => x ∈ E i)
    use S
    constructor
    · simp only [R, Set.mem_inter_iff, Set.mem_iInter, S]
      constructor
      · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hi
      · intro i hi; simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hi; exact hi
    · intro T hT
      ext i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [R, Set.mem_inter_iff, Set.mem_iInter] at hT
      obtain ⟨hT_in, hT_out⟩ := hT
      constructor
      · intro hi; exact hT_in i hi
      · intro hxi; by_contra hni
        have hni' : i ∈ Tᶜ := Finset.mem_compl.mpr hni
        exact hT_out i hni' hxi
  -- {g > t} = ⋃_{S : ∑_{i ∈ S} c_i > t} R_S
  have h_eq : {x | g x > t} = ⋃ S ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun S => ∑ i ∈ S, c i > t), R S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hgx
      obtain ⟨S, hxS, _⟩ := h_partition x
      refine ⟨S, ?_, hxS⟩; rw [hg_const S x hxS] at hgx; exact hgx
    · intro ⟨S, hS_gt, hxS⟩; rw [hg_const S x hxS]; exact hS_gt
  rw [h_eq]
  apply LebesgueMeasurable.finset_union; intro S _; exact hR_meas S

end UnsignedMeasurable.TFAE_helpers
