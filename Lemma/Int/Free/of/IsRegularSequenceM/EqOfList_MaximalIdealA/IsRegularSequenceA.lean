import Mathlib
import sympy.Basic
open scoped Pointwise
open RingTheory.Sequence
open Module


private lemma ofList_cons
  [CommRing A]
  (r : A) (rs : List A) :
-- imply
  Ideal.ofList (r :: rs) = Ideal.span {r} ⊔ Ideal.ofList rs := by
-- proof
  rw [show r :: rs = [r] ++ rs from rfl, Ideal.ofList_append]
  congr 1
  simp [Ideal.ofList]

private lemma map_mk_maximalIdeal
  [CommRing A] [IsLocalRing A]
  (I : Ideal A)
  [IsLocalRing (A ⧸ I)]
-- given
  (hI : I ≠ ⊤) :
-- imply
  (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk I) = IsLocalRing.maximalIdeal (A ⧸ I) := by
-- proof
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  obtain h | h := Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj (IsLocalRing.maximalIdeal.isMaximal A)
  ·
    exfalso
    have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk I)) h
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hI)] at h2
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top h2
  · exact IsLocalRing.eq_maximalIdeal h

private lemma free_of_free_quotSMulTop
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
  {r : A} [Module.Free (A ⧸ Ideal.span {r}) (QuotSMulTop r M)]
-- given
  (hr𝔪 : r ∈ IsLocalRing.maximalIdeal A)
  (hr : IsSMulRegular M r) :
-- imply
  Module.Free A M := by
-- proof
  classical
  set A' := A ⧸ Ideal.span {r}
  set N := QuotSMulTop r M
  have : Module.Finite A' N := Module.Finite.of_restrictScalars_finite A A' N
  let ι := Module.Free.ChooseBasisIndex A' N
  have : Fintype ι := Module.Free.ChooseBasisIndex.fintype A' N
  let b := Module.Free.chooseBasis A' N
  choose v hv using fun i => Submodule.Quotient.mk_surjective (r • ⊤ : Submodule A M) (b i)
  let φ : (ι → A) →ₗ[A] M := Fintype.linearCombination A v
  have hmap : (Submodule.span A (Set.range v)).map (r • ⊤ : Submodule A M).mkQ = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp]
    have hcomp : ((r • ⊤ : Submodule A M).mkQ ∘ v) = b := funext hv
    rw [hcomp, ← Submodule.restrictScalars_span A A' Ideal.Quotient.mk_surjective (Set.range b), b.span_eq,
      Submodule.restrictScalars_top]
  have hsup : Submodule.span A (Set.range v) ⊔ r • ⊤ = ⊤ := by
    have := Submodule.comap_map_eq (r • ⊤ : Submodule A M).mkQ (Submodule.span A (Set.range v))
    rw [hmap, Submodule.comap_top, Submodule.ker_mkQ] at this
    apply this.symm
  have hr_le : (r • ⊤ : Submodule A M) ≤ IsLocalRing.maximalIdeal A • ⊤ := by
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hr𝔪)
  have hspan : Submodule.span A (Set.range v) = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal]; apply bot_ne_top) ?_)
    calc
      _ = Submodule.span A (Set.range v) ⊔ r • ⊤ := hsup.symm
      _ ≤ Submodule.span A (Set.range v) ⊔ IsLocalRing.maximalIdeal A • ⊤ :=
        sup_le_sup_left hr_le _
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]
  set K := LinearMap.ker φ
  have hK : K ≤ Ideal.span {r} • K := by
    intro c hc
    have hc0 : φ c = 0 := hc
    have h1 : ∑ i, (Ideal.Quotient.mk (Ideal.span {r}) (c i)) • b i = 0 := by
      have := congrArg (r • ⊤ : Submodule A M).mkQ hc0
      rw [map_zero] at this
      rw [← this]
      simp only [φ, Fintype.linearCombination_apply, map_sum, map_smul, Submodule.mkQ_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    have h2 : ∀ i, Ideal.Quotient.mk (Ideal.span {r}) (c i) = 0 :=
      Fintype.linearIndependent_iff.mp b.linearIndependent _ h1
    have h3 : ∀ i, ∃ d, d * r = c i := fun i =>
      Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp (h2 i))
    choose d hd using h3
    have hcd : c = r • d := by funext i; rw [Pi.smul_apply, smul_eq_mul, mul_comm, hd]
    have hdK : d ∈ K := by
      show φ d = 0
      apply hr
      show r • φ d = r • 0
      rw [smul_zero, ← map_smul, ← hcd, hc0]
    rw [hcd]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) hdK
  have hKfg : K.FG := IsNoetherian.noetherian K
  have hKbot : K = ⊥ := by
    refine le_bot_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot hKfg
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal]; apply bot_ne_top) ?_)
    calc
      _ ≤ Ideal.span {r} • K := hK
      _ ≤ IsLocalRing.maximalIdeal A • K :=
        Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hr𝔪)
      _ ≤ ⊥ ⊔ IsLocalRing.maximalIdeal A • K := le_sup_right
  have hinj : Function.Injective φ := LinearMap.ker_eq_bot.mp hKbot
  refine Module.Free.of_equiv (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩)

private lemma free_of_isWeaklyRegular_aux
  (n : ℕ) :
-- imply
  ∀ (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (rs : List A), rs.length = n →
    Ideal.ofList rs = IsLocalRing.maximalIdeal A →
    ∀ (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M],
      IsWeaklyRegular M rs → Module.Free A M := by
-- proof
  induction n with
  | zero =>
    intro A _ _ _ rs hlen hspan M _ _ _ _
    obtain rfl : rs = [] := List.eq_nil_of_length_eq_zero hlen
    rw [Ideal.ofList_nil] at hspan
    have hF : IsField A := (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hspan.symm
    let _ := hF.toField
    exact Module.Free.of_divisionRing A M
  | succ n ih =>
    intro A _ _ _ rs hlen hspan M _ _ _ hM
    have hrsne : rs ≠ [] := fun h => by simp [h] at hlen
    obtain ⟨r, rs', rfl⟩ := List.exists_cons_of_ne_nil hrsne
    rw [isWeaklyRegular_cons_iff'] at hM
    obtain ⟨hr, hM'⟩ := hM
    have hr𝔪 : r ∈ IsLocalRing.maximalIdeal A := hspan ▸ Ideal.subset_span (by simp)
    have hne : Ideal.span {r} ≠ ⊤ :=
      fun h => (IsLocalRing.mem_maximalIdeal r).mp hr𝔪 (Ideal.span_singleton_eq_top.mp h)
    have : Nontrivial (A ⧸ Ideal.span {r}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (A ⧸ Ideal.span {r}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have hspan' :
      Ideal.ofList (rs'.map (Ideal.Quotient.mk (Ideal.span {r}))) =
        IsLocalRing.maximalIdeal (A ⧸ Ideal.span {r}) := by
      rw [← Ideal.map_ofList, ← map_mk_maximalIdeal _ hne, ← hspan, ofList_cons, Ideal.map_sup,
        Ideal.map_quotient_self, bot_sup_eq]
    have : Module.Finite (A ⧸ Ideal.span {r}) (QuotSMulTop r M) :=
      Module.Finite.of_restrictScalars_finite A _ _
    have := ih (A ⧸ Ideal.span {r}) _ (by simpa using hlen) hspan' (QuotSMulTop r M) hM'
    exact free_of_free_quotSMulTop M hr𝔪 hr

/--
[Module_free_of_isRegular_of_span_eq_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_free_of_isRegular_of_span_eq_maximalIdeal.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  {rs : List A}
-- given
  (_ : RingTheory.Sequence.IsRegular A rs)
  (hspan : Ideal.ofList rs = IsLocalRing.maximalIdeal A)
  (hM : RingTheory.Sequence.IsRegular M rs) :
-- imply
  Module.Free A M :=
-- proof
  free_of_isWeaklyRegular_aux rs.length A rs rfl hspan M hM.toIsWeaklyRegular


-- created on 2026-10-24
