import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Instance.Probability.Process.HiddenMarkovSequence
import Notation.Fun
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Instance.Data.Nat.Fun
open MeasureTheory ProbabilityTheory Random Fun


/--
If every process prefix `s[:n]` admits a density against the product reference
measure, then so does the joint `(s[k], s[:k])`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → 𝒮}
-- given
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮)) :
-- imply
  ∀ k, SinglePSpace π (s k, s[:k]) := by
-- proof
  intro k
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k)
  have hfun :
    ((s k, s[:k]) : Ω → 𝒮 × FunSlice.Vec 𝒮 ⟨0, ↑k, 1⟩) =
      e ∘ (s[:k.succ] : Ω → Fin k.succ → 𝒮) := by
    funext ω
    apply Prod.ext
    ·
      have hstart : (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat = 0 := rfl
      simp only [Function.getSlice]
      change s k ω =
        s ((Fin.last k).val + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat) ω
      rw [hstart, Fin.val_last]
      simp
    ·
      funext j
      have hstart0 : (⟨0, ↑k, 1⟩ : Slice).start.toNat = 0 := rfl
      simp only [JointRandomSymbol, Function.comp_apply, Function.getSlice]
      have hrhs :
        (e (FunSlice.slice s ⟨0, ↑k.succ, 1⟩ ω)).2 j =
          FunSlice.slice s ⟨0, ↑k.succ, 1⟩ ω
            ((Fin.last k).succAbove j) :=
        rfl
      rw [hrhs, Fin.succAbove_last]
      change s (j.val + (⟨0, ↑k, 1⟩ : Slice).start.toNat) ω =
        s (j.castSucc.val + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat) ω
      have hidx : (j : ℕ) + (⟨0, ↑k, 1⟩ : Slice).start.toNat =
        (j.castSucc : ℕ) + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat := by
        let jn : ℕ := j
        let jn' : ℕ := j.castSucc
        have hj' : jn' = jn := Fin.val_castSucc j
        change jn + (⟨0, ↑k, 1⟩ : Slice).start.toNat =
          jn' + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat
        rw [hstart0, hj']
      rw [hidx]
  have hcomp : SinglePSpace π (e ∘ (s[:k.succ] : Ω → Fin k.succ → 𝒮)) := by
    obtain ⟨ρ, hρm, hlaw⟩ := (hP k.succ).exists_distribution
    let ρ' : 𝒮 × (Fin k → 𝒮) → ENNReal := ρ ∘ e.symm
    have hρ'm : Measurable ρ' := hρm.comp e.symm.measurable
    have hX_ae : AEMeasurable (s[:k.succ] : Ω → Fin k.succ → 𝒮) π :=
      (hP k.succ).aemeasurable
    have hY_ae : AEMeasurable (e ∘ (s[:k.succ] : Ω → Fin k.succ → 𝒮)) π :=
      e.measurable.comp_aemeasurable hX_ae
    have hmap : π.map (e ∘ (s[:k.succ] : Ω → Fin k.succ → 𝒮)) =
        (π.map (s[:k.succ] : Ω → Fin k.succ → 𝒮)).map e :=
      (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hX_ae).symm
    have he : MeasurePreserving e
      (ReferenceMeasure.measure (α := Fin k.succ → 𝒮))
      (ReferenceMeasure.measure (α := 𝒮 × (Fin k → 𝒮))) := by
      change MeasurePreserving e
        (Measure.pi fun _ : Fin k.succ => ReferenceMeasure.measure (α := 𝒮))
        ((ReferenceMeasure.measure (α := 𝒮)).prod
          (Measure.pi fun _ : Fin k => ReferenceMeasure.measure (α := 𝒮)))
      exact measurePreserving_piFinSuccAbove
        (fun _ : Fin k.succ => ReferenceMeasure.measure (α := 𝒮)) (Fin.last k)
    have hwd :
      ((ReferenceMeasure.measure (α := Fin k.succ → 𝒮)).withDensity ρ).map e =
        (ReferenceMeasure.measure (α := 𝒮 × (Fin k → 𝒮))).withDensity ρ' := by
      ext t ht
      rw [Measure.map_apply e.measurable ht,
        withDensity_apply _ (e.measurable ht),
        withDensity_apply _ ht, ← he.map_eq,
        setLIntegral_map ht hρ'm e.measurable]
      refine setLIntegral_congr_fun (e.measurable ht) ?_
      intro x _
      change ρ x = ρ (e.symm (e x))
      rw [e.symm_apply_apply]
    refine {
      toIsProbabilityMeasure := inferInstance
      aemeasurable := hY_ae
      exists_distribution := ⟨ρ', hρ'm, ?_⟩
    }
    rw [hmap, hlaw, hwd]
  rwa [← hfun] at hcomp


-- created on 2026-11-18
-- updated on 2026-11-23
