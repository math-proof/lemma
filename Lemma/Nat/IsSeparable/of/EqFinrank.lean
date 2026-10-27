import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean)
-/
@[path]
private lemma main
  [Field E] [Field F] [Algebra E F] [FiniteDimensional E F]
  {p : ℕ} [Fact p.Prime] [CharP F p]
  {y : E}
-- given
  (hdeg : Module.finrank (frobenius F p).fieldRange F = p)
  (hy : algebraMap E F y ∉ (frobenius F p).fieldRange) :
-- imply
  Algebra.IsSeparable E F := by
-- proof
  let S : Subfield F := (frobenius F p).fieldRange
  have : IsSimpleOrder (IntermediateField S F) :=
    IntermediateField.isSimpleOrder_of_finrank_prime S F (by rw [hdeg]; apply Fact.out)
  let D := KaehlerDifferential.D E F
  have hDS : ∀ s : F, s ∈ S → D s = 0 := by
    intro s hs
    obtain ⟨a, rfl⟩ := RingHom.mem_fieldRange.mp hs
    rw [frobenius_def, D.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hDy : D (algebraMap E F y) = 0 := D.map_algebraMap y
  let Z : IntermediateField S F :=
    { carrier := {z | D z = 0}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [D.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      one_mem' := D.map_one_eq_zero
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_add, ha, hb, add_zero]
      zero_mem' := map_zero D
      algebraMap_mem' := fun s => hDS _ s.2
      inv_mem' := by
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz ⊢
        rw [D.leibniz_inv, hz, smul_zero] }
  have hyZ : IntermediateField.adjoin S {algebraMap E F y} ≤ Z :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hDy)
  have hZ : Z = ⊤ := by
    obtain h | h := IsSimpleOrder.eq_bot_or_eq_top (IntermediateField.adjoin S {algebraMap E F y})
    ·
      exfalso
      apply hy
      have hmem : algebraMap E F y ∈ (⊥ : IntermediateField S F) :=
        h ▸ IntermediateField.mem_adjoin_simple_self S (algebraMap E F y)
      obtain ⟨s, hs⟩ := IntermediateField.mem_bot.mp hmem
      rw [← hs]
      apply s.2
    ·
      rw [h] at hyZ
      apply top_le_iff.mp hyZ
  have hD0 : ∀ z : F, D z = 0 := fun z => by
    apply hZ ▸ IntermediateField.mem_top
  have : Subsingleton (KaehlerDifferential E F) := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    have hle : Submodule.span F (Set.range D) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨z, rfl⟩
      apply (Submodule.mem_bot F).mpr (hD0 z)
    apply (Submodule.mem_bot F).mp
    apply hle
    rw [KaehlerDifferential.span_range_derivation]
    apply trivial
  have : Algebra.FormallyUnramified E F := ⟨inferInstance⟩
  apply Algebra.FormallyUnramified.isSeparable


-- created on 2026-10-12
