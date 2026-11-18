import Lemma.Random.SinglePSpace.SinglePSpace.of.SinglePSpace
import Instance.Probability.Process.HiddenMarkovSequence.Part2
import Notation.Fun
import Initialize.Tactic.Attr.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory ProbabilityTheory Random Fun


/--
Transfer a `SinglePSpace` hypothesis along a measure-preserving measurable
equivalence of the codomain.
-/
private lemma SinglePSpace_map_equiv
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [ReferenceMeasure β]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {X : Ω → α}
-- given
  (e : α ≃ᵐ β)
  (he : MeasurePreserving e
    (ReferenceMeasure.measure (α := α))
    (ReferenceMeasure.measure (α := β)))
  (hX : SinglePSpace π X) :
-- imply
  SinglePSpace π (e ∘ X) := by
-- proof
  obtain ⟨ρ, hρm, hlaw⟩ := hX.exists_distribution
  let ρ' : β → ENNReal := ρ ∘ e.symm
  have hρ'm : Measurable ρ' := hρm.comp e.symm.measurable
  have hX_ae : AEMeasurable X π := hX.aemeasurable
  have hY_ae : AEMeasurable (e ∘ X) π := e.measurable.comp_aemeasurable hX_ae
  have hmap : π.map (e ∘ X) = (π.map X).map e :=
    (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hX_ae).symm
  have hwd :
    ((ReferenceMeasure.measure (α := α)).withDensity ρ).map e =
      (ReferenceMeasure.measure (α := β)).withDensity ρ' := by
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

/--
The length-`k + 1` prefix is, up to peeling the last coordinate, the joint
`(s[k], s[:k])`.
-/
private lemma fun_Get_GetSlice_eq_piFinSuccAbove_comp_GetSlice_succ
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {s : ℕ ⇀ Ω → 𝒮}
  {k : ℕ} :
-- imply
  ((s[k], s[:k]) : Ω → 𝒮 × FunSlice.Vec 𝒮 ⟨0, ↑k, 1⟩) =
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k) ∘
      (s[:k.succ] : Ω → Fin k.succ → 𝒮) := by
-- proof
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k)
  funext ω
  apply Prod.ext
  ·
    have hstart : (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat = 0 := rfl
    simp only [Fun.getSlice, Function.getSlice]
    change s[k] ω =
      s.toFun ((Fin.last k).val + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat) ω
    rw [hstart, Fin.val_last]
    simp
  ·
    funext j
    have hstart0 : (⟨0, ↑k, 1⟩ : Slice).start.toNat = 0 := rfl
    simp only [JointRandomSymbol, Function.comp_apply, Fun.getSlice,
      Function.getSlice]
    have hrhs :
      (e (FunSlice.slice s.toFun ⟨0, ↑k.succ, 1⟩ ω)).2 j =
        FunSlice.slice s.toFun ⟨0, ↑k.succ, 1⟩ ω
          ((Fin.last k).succAbove j) :=
      rfl
    rw [hrhs, Fin.succAbove_last]
    change s.toFun (j.val + (⟨0, ↑k, 1⟩ : Slice).start.toNat) ω =
      s.toFun (j.castSucc.val + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat) ω
    have hidx : (j : ℕ) + (⟨0, ↑k, 1⟩ : Slice).start.toNat =
      (j.castSucc : ℕ) + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat := by
      let jn : ℕ := j
      let jn' : ℕ := j.castSucc
      have hj' : jn' = jn := Fin.val_castSucc j
      change jn + (⟨0, ↑k, 1⟩ : Slice).start.toNat =
        jn' + (⟨0, ↑k.succ, 1⟩ : Slice).start.toNat
      rw [hstart0, hj']
    rw [hidx]

private lemma measurePreserving_piFinSuccAbove_last
  [ReferenceMeasure 𝒮]
  {k : ℕ} :
-- imply
  MeasurePreserving
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k))
    (ReferenceMeasure.measure (α := Fin k.succ → 𝒮))
    (ReferenceMeasure.measure (α := 𝒮 × (Fin k → 𝒮))) := by
-- proof
  change MeasurePreserving
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k))
    (Measure.pi fun _ : Fin k.succ => ReferenceMeasure.measure (α := 𝒮))
    ((ReferenceMeasure.measure (α := 𝒮)).prod
      (Measure.pi fun _ : Fin k => ReferenceMeasure.measure (α := 𝒮)))
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin k.succ => ReferenceMeasure.measure (α := 𝒮)) (Fin.last k)

/--
`SinglePSpace` of the length-`k + 1` prefix transfers along the measurable
equivalence that peels off the last coordinate, yielding a joint density of
`(s[k], s[:k])`.
-/
private lemma SinglePSpace_Get_GetSlice_of_GetSlice_succ
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
  {k : ℕ}
-- given
  (hP : SinglePSpace π (s[:k.succ] : Ω → Fin k.succ → 𝒮)) :
-- imply
  SinglePSpace π (s[k], s[:k]) := by
-- proof
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k)
  have hfun := fun_Get_GetSlice_eq_piFinSuccAbove_comp_GetSlice_succ (s := s) (k := k)
  have hcomp : SinglePSpace π (e ∘ (s[:k.succ] : Ω → Fin k.succ → 𝒮)) :=
    SinglePSpace_map_equiv e measurePreserving_piFinSuccAbove_last hP
  rwa [← hfun] at hcomp

/--
A joint density of `(s[k + 1], s[:k.succ])` transfers to a joint density of
the adjacent pair `(s[k + 1], s[k])`, by peeling the last coordinate of the
prefix and dropping the earlier coordinates.
-/
private lemma SinglePSpace_Get_succ_Get_of_Get_succ_GetSlice
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
  {k : ℕ}
-- given
  (hP : SinglePSpace π (s[k + 1], s[:k.succ])) :
-- imply
  SinglePSpace π (s[k + 1], s[k]) := by
-- proof
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin k.succ => 𝒮) (Fin.last k)
  let e_pair := (MeasurableEquiv.refl 𝒮).prodCongr e
  let e_tot := e_pair.trans (MeasurableEquiv.prodAssoc (α := 𝒮) (β := 𝒮)
    (γ := Fin k → 𝒮)).symm
  have hfun_peel :=
    fun_Get_GetSlice_eq_piFinSuccAbove_comp_GetSlice_succ (s := s) (k := k)
  have hfun :
    (fun ω =>
      ((s[k + 1] ω, s[k] ω), (s[:k] : Ω → Fin k → 𝒮) ω)) =
      e_tot ∘ (s[k + 1], (s[:k.succ] : Ω → Fin k.succ → 𝒮)) := by
    funext ω
    have hv :
      e ((s[:k.succ] : Ω → Fin k.succ → 𝒮) ω) =
        ((s[k], s[:k]) : Ω → 𝒮 × (Fin k → 𝒮)) ω :=
      (congrFun hfun_peel ω).symm
    change
      ((s[k + 1] ω, s[k] ω), (s[:k] : Ω → Fin k → 𝒮) ω) =
        (MeasurableEquiv.prodAssoc (α := 𝒮) (β := 𝒮)
          (γ := Fin k → 𝒮)).symm
          (s[k + 1] ω, e ((s[:k.succ] : Ω → Fin k.succ → 𝒮) ω))
    rw [hv]
    rfl
  have he_pair :
    MeasurePreserving e_pair
      (ReferenceMeasure.measure (α := 𝒮 × (Fin k.succ → 𝒮)))
      (ReferenceMeasure.measure (α := 𝒮 × 𝒮 × (Fin k → 𝒮))) := by
    change MeasurePreserving e_pair
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        (ReferenceMeasure.measure (α := Fin k.succ → 𝒮)))
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        (ReferenceMeasure.measure (α := 𝒮 × (Fin k → 𝒮))))
    exact (MeasurePreserving.id _).prod measurePreserving_piFinSuccAbove_last
  have he_tot :
    MeasurePreserving e_tot
      (ReferenceMeasure.measure (α := 𝒮 × (Fin k.succ → 𝒮)))
      (ReferenceMeasure.measure (α := Prod (𝒮 × 𝒮) (Fin k → 𝒮))) := by
    change MeasurePreserving e_tot
      ((ReferenceMeasure.measure (α := 𝒮)).prod
        (ReferenceMeasure.measure (α := Fin k.succ → 𝒮)))
      (((ReferenceMeasure.measure (α := 𝒮)).prod
          (ReferenceMeasure.measure (α := 𝒮))).prod
        (ReferenceMeasure.measure (α := Fin k → 𝒮)))
    exact (measurePreserving_prodAssoc
        (ReferenceMeasure.measure (α := 𝒮))
        (ReferenceMeasure.measure (α := 𝒮))
        (ReferenceMeasure.measure (α := Fin k → 𝒮))).symm.comp he_pair
  have hassoc : SinglePSpace π (e_tot ∘ (s[k + 1], s[:k.succ])) :=
    SinglePSpace_map_equiv e_tot he_tot hP
  have hassoc' :
    SinglePSpace π
      (fun ω =>
        ((s[k + 1] ω, s[k] ω), (s[:k] : Ω → Fin k → 𝒮) ω)) := by
    rwa [← hfun] at hassoc
  exact SinglePSpace.of.SinglePSpace.fst hassoc'

/--
If every process prefix `s[:n]` admits a density against the product reference
measure, then so do the joints `(s[k], s[:k])` and `(s[k + 1], s[k])`.
| attributes | lemma |
| :---: | :---: |
| path | Random.All_SinglePSpaceJointGet__GetSlice.All_SinglePSpaceJointGet_Add_1_Get.of.All_SinglePSpaceGetSlice |
| And.left | Random.All_SinglePSpaceJointGet__GetSlice.of.All_SinglePSpaceGetSlice |
| And.right | Random.All_SinglePSpaceJointGet_Add_1_Get.of.All_SinglePSpaceGetSlice |
-/
@[path, And.left, And.right]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮)) :
-- imply
  (∀ k, SinglePSpace π (s[k], s[:k])) ∧
    ∀ k, SinglePSpace π (s[k + 1], s[k]) := by
-- proof
  refine ⟨?_, ?_⟩
  ·
    intro k
    exact SinglePSpace_Get_GetSlice_of_GetSlice_succ (hP k.succ)
  ·
    intro k
    exact SinglePSpace_Get_succ_Get_of_Get_succ_GetSlice
      (SinglePSpace_Get_GetSlice_of_GetSlice_succ (hP (k + 1).succ))


-- created on 2026-11-18
