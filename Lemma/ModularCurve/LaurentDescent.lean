import Lemma.ModularCurve.GeometricBaseChange

noncomputable section

open HahnSeries IntermediateField

namespace ModularCurve

section Descent

universe uE

variable {E L : Type*} [Field E] [Field L] [Algebra ℚ E] [Algebra ℚ L]
variable (ι : E →+* L) (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

omit [Field L] [Algebra ℚ L] in

theorem comp_algebraMap_rat_eq {L : Type*} [CommRing L] [Algebra ℚ L] (ι : E →+* L) :
    ι.comp (algebraMap ℚ E) = algebraMap ℚ L :=
  RingHom.ext_rat _ _

omit [Algebra ℚ E] [Algebra ℚ L] in

theorem coeffMap_algebraMap_apply (c : E) :
    coeffMap ι (algebraMap E (LaurentSeries E) c) = algebraMap L (LaurentSeries L) (ι c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_coeffEmb_apply (x : LaurentSeries ℚ) : coeffMap ι (coeffEmb E x) = coeffEmb L x := by
  change coeffMap ι (coeffMap (algebraMap ℚ E) x) = coeffMap (algebraMap ℚ L) x
  rw [coeffMap_coeffMap, comp_algebraMap_rat_eq]

theorem coeffMap_mem_laurentBaseChange_of_mem {x : LaurentSeries E} (hx : x ∈ laurentBaseChange E F₀) :
    coeffMap ι x ∈ laurentBaseChange L F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap_apply]
        exact (laurentBaseChange L F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb_apply ι]
        exact coeffEmb_mem_laurentBaseChange L hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

def laurentDescent : laurentBaseChange E F₀ →+* laurentBaseChange L F₀ :=
  ((coeffMap ι).comp (SubringClass.subtype (laurentBaseChange E F₀))).codRestrict (laurentBaseChange L F₀)
    fun x => coeffMap_mem_laurentBaseChange_of_mem ι F₀ x.2

@[simp]
theorem coe_laurentDescent_apply (x : laurentBaseChange E F₀) :
    (laurentDescent ι F₀ x : LaurentSeries L) = coeffMap ι x :=
  rfl

theorem coeff_laurentDescent_apply (x : laurentBaseChange E F₀) (k : ℤ) :
    (laurentDescent ι F₀ x : LaurentSeries L).coeff k = ι ((x : LaurentSeries E).coeff k) :=
  rfl

theorem laurentDescent_injective : Function.Injective (laurentDescent ι F₀) :=
  (laurentDescent ι F₀).injective

theorem laurentDescent_algebraMap (c : E) :
    laurentDescent ι F₀ (algebraMap E (laurentBaseChange E F₀) c) = algebraMap L (laurentBaseChange L F₀) (ι c) :=
  Subtype.ext (coeffMap_algebraMap_apply ι c)

theorem laurentDescent_coeffEmb {f : LaurentSeries ℚ} (hf : f ∈ F₀) :
    laurentDescent ι F₀ ⟨coeffEmb E f, coeffEmb_mem_laurentBaseChange E hf⟩ =
      ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L hf⟩ :=
  Subtype.ext (coeffMap_coeffEmb_apply ι f)

theorem laurentDescent_laurentDescent {L' : Type*} [Field L'] [Algebra ℚ L'] (κ : L →+* L')
    (x : laurentBaseChange E F₀) :
    laurentDescent κ F₀ (laurentDescent ι F₀ x) = laurentDescent (κ.comp ι) F₀ x :=
  Subtype.ext (coeffMap_coeffMap κ ι x)

theorem laurentDescent_geomAut [Algebra.IsAlgebraic ℚ E] [Algebra.IsAlgebraic ℚ L] (σ : F₀ ≃ₐ[ℚ] F₀)
    (x : laurentBaseChange E F₀) :
    laurentDescent ι F₀ (geomAut E F₀ σ x) = geomAut L F₀ σ (laurentDescent ι F₀ x) := by

  suffices h : ∀ (y : LaurentSeries E) (hy : y ∈ Subfield.closure
      (Set.range (algebraMap E (LaurentSeries E)) ∪ (⇑(coeffEmb E) '' (F₀ : Set (LaurentSeries ℚ))))),
      laurentDescent ι F₀ (geomAut E F₀ σ ⟨y, hy⟩) = geomAut L F₀ σ (laurentDescent ι F₀ ⟨y, hy⟩) from
    h x.1 x.2
  intro y hy
  induction hy using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨a, rfl⟩ | ⟨f, hf, rfl⟩
      · change laurentDescent ι F₀ (geomAut E F₀ σ (algebraMap E (laurentBaseChange E F₀) a)) =
          geomAut L F₀ σ (laurentDescent ι F₀ (algebraMap E (laurentBaseChange E F₀) a))
        rw [AlgEquiv.commutes, laurentDescent_algebraMap, AlgEquiv.commutes]
      · change laurentDescent ι F₀ (geomAut E F₀ σ ⟨coeffEmb E f, coeffEmb_mem_laurentBaseChange E hf⟩) =
          geomAut L F₀ σ (laurentDescent ι F₀ ⟨coeffEmb E f, coeffEmb_mem_laurentBaseChange E hf⟩)
        rw [geomAut_coeffEmb E F₀ σ ⟨f, hf⟩, laurentDescent_coeffEmb ι F₀ hf,
          laurentDescent_coeffEmb ι F₀ (σ ⟨f, hf⟩).2, geomAut_coeffEmb L F₀ σ ⟨f, hf⟩]
  | one =>
      change laurentDescent ι F₀ (geomAut E F₀ σ 1) = geomAut L F₀ σ (laurentDescent ι F₀ 1)
      simp only [map_one]
  | add u v hu hv ihu ihv =>
      have e1 : (⟨u + v, add_mem hu hv⟩ : laurentBaseChange E F₀) = ⟨u, hu⟩ + ⟨v, hv⟩ := rfl
      rw [e1, map_add, map_add, map_add, map_add, ihu, ihv]
  | neg u hu ihu =>
      have e1 : (⟨-u, neg_mem hu⟩ : laurentBaseChange E F₀) = -⟨u, hu⟩ := rfl
      rw [e1, map_neg, map_neg, map_neg, map_neg, ihu]
  | inv u hu ihu =>
      have e1 : (⟨u⁻¹, inv_mem hu⟩ : laurentBaseChange E F₀) = (⟨u, hu⟩ : laurentBaseChange E F₀)⁻¹ := rfl
      rw [e1, map_inv₀, map_inv₀, map_inv₀, map_inv₀, ihu]
  | mul u v hu hv ihu ihv =>
      have e1 : (⟨u * v, mul_mem hu hv⟩ : laurentBaseChange E F₀) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_mul, ihu, ihv]

theorem exists_finset_forall_exists_laurentDescent_eq (y : laurentBaseChange L F₀) :
    ∃ s : Finset L, ∀ (E : Type uE) [Field E] [Algebra ℚ E] (ι : E →+* L), (↑s ⊆ Set.range ι) →
      ∃ x : laurentBaseChange E F₀, laurentDescent ι F₀ x = y := by
  classical
  obtain ⟨y, hy⟩ := y

  suffices h : ∃ s : Finset L, ∀ (E : Type uE) [Field E] [Algebra ℚ E] (ι : E →+* L), (↑s ⊆ Set.range ι) →
      ∃ x : laurentBaseChange E F₀, (laurentDescent ι F₀ x : LaurentSeries L) = y from by
    obtain ⟨s, hs⟩ := h
    exact ⟨s, fun E _ _ ι hsub => by
      obtain ⟨x, hx⟩ := hs E ι hsub
      exact ⟨x, Subtype.ext hx⟩⟩
  have hy' : y ∈ Subfield.closure
      (Set.range (algebraMap L (LaurentSeries L)) ∪ (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) := hy
  clear hy
  induction hy' using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨a, rfl⟩ | ⟨f, hf, rfl⟩
      · refine ⟨{a}, fun E _ _ ι hsub => ?_⟩
        obtain ⟨b, hb⟩ := hsub (Finset.mem_coe.mpr (Finset.mem_singleton_self a))
        exact ⟨algebraMap E _ b, by rw [laurentDescent_algebraMap, hb]; rfl⟩
      · exact ⟨∅, fun E _ _ ι _ =>
          ⟨⟨coeffEmb E f, coeffEmb_mem_laurentBaseChange E hf⟩, coeffMap_coeffEmb_apply ι f⟩⟩
  | one => exact ⟨∅, fun E _ _ ι _ => ⟨1, by rw [map_one]; rfl⟩⟩
  | add u v _ _ ihu ihv =>
      obtain ⟨s, hs⟩ := ihu
      obtain ⟨t, ht⟩ := ihv
      refine ⟨s ∪ t, fun E _ _ ι hsub => ?_⟩
      rw [Finset.coe_union] at hsub
      obtain ⟨a, ha⟩ := hs E ι (Set.subset_union_left.trans hsub)
      obtain ⟨b, hb⟩ := ht E ι (Set.subset_union_right.trans hsub)
      exact ⟨a + b, by rw [map_add]; exact congrArg₂ (· + ·) ha hb⟩
  | neg u _ ihu =>
      obtain ⟨s, hs⟩ := ihu
      refine ⟨s, fun E _ _ ι hsub => ?_⟩
      obtain ⟨a, ha⟩ := hs E ι hsub
      exact ⟨-a, by rw [map_neg]; exact congrArg (- ·) ha⟩
  | inv u _ ihu =>
      obtain ⟨s, hs⟩ := ihu
      refine ⟨s, fun E _ _ ι hsub => ?_⟩
      obtain ⟨a, ha⟩ := hs E ι hsub
      exact ⟨a⁻¹, by rw [map_inv₀]; exact congrArg (· ⁻¹) ha⟩
  | mul u v _ _ ihu ihv =>
      obtain ⟨s, hs⟩ := ihu
      obtain ⟨t, ht⟩ := ihv
      refine ⟨s ∪ t, fun E _ _ ι hsub => ?_⟩
      rw [Finset.coe_union] at hsub
      obtain ⟨a, ha⟩ := hs E ι (Set.subset_union_left.trans hsub)
      obtain ⟨b, hb⟩ := ht E ι (Set.subset_union_right.trans hsub)
      exact ⟨a * b, by rw [map_mul]; exact congrArg₂ (· * ·) ha hb⟩

end Descent

end ModularCurve

end

#print axioms ModularCurve.laurentDescent_geomAut
#print axioms ModularCurve.exists_finset_forall_exists_laurentDescent_eq
