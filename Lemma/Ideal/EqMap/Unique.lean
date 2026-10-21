import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {S : Type u} [CommRing S] {ι : Type} (e : ι → S)
noncomputable abbrev chart (i : ι) : Spec (CommRingCat.of (S ⧸ Ideal.span {1 - e i})) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e i})))
private lemma isLocalization_away (he : OrthogonalIdempotents e) (i : ι) :
  IsLocalization.Away (e i) (S ⧸ Ideal.span {1 - e i}) :=
  IsLocalization.away_of_isIdempotentElem (he.idem i)
    (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]) Ideal.Quotient.mk_surjective
private lemma range_chart (i : ι) :
  Set.range (chart e i).base = PrimeSpectrum.zeroLocus (Ideal.span {1 - e i} : Ideal S) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {1 - e i}))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
private lemma mem_range_chart_iff (i : ι) (x : PrimeSpectrum S) :
  x ∈ Set.range (chart e i).base ↔ 1 - e i ∈ x.asIdeal := by
  rw [range_chart]
  change ((Ideal.span {1 - e i} : Ideal S) : Set S) ⊆ x.asIdeal ↔ _
  rw [SetLike.coe_subset_coe, Ideal.span_singleton_le_iff_mem]
variable [Fintype ι]
private lemma isOpenImmersion_chart (he : CompleteOrthogonalIdempotents e) (i : ι) : IsOpenImmersion (chart e i) := by
  let _ := isLocalization_away e he.toOrthogonalIdempotents i
  apply IsOpenImmersion.of_isLocalization (e i)
private lemma covers (he : CompleteOrthogonalIdempotents e) (x : PrimeSpectrum S) :
  ∃ (i : ι) (y : ↥(Spec (CommRingCat.of (S ⧸ Ideal.span {1 - e i})))), (chart e i).base y = x := by
  classical
  have hsum : ∑ i, e i ∉ x.asIdeal := by
    rw [he.complete]
    intro h
    apply x.2.ne_top
    apply (Ideal.eq_top_iff_one _).mpr h
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, e i ∉ x.asIdeal := by
    by_contra h
    push Not at h
    apply hsum (Ideal.sum_mem _ fun i hi => h i hi)
  have hmem : 1 - e i ∈ x.asIdeal := by
    refine (x.2.mem_or_mem ?_).resolve_left hi
    rw [mul_sub, mul_one, (he.idem i).eq, sub_self]
    apply x.asIdeal.zero_mem
  obtain ⟨y, hy⟩ := (mem_range_chart_iff e i x).mpr hmem
  exact ⟨i, y, hy⟩
private lemma disjoint_range_chart (he : CompleteOrthogonalIdempotents e) {i k : ι} (hik : i ≠ k) :
  Disjoint (Set.range (chart e i).base) (Set.range (chart e k).base) := by
  rw [Set.disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  have hx := (mem_range_chart_iff e i x).mp hx
  have hx' := (mem_range_chart_iff e k x).mp hx'
  have h1 : (1 : S) = (1 - e i) + (1 - e k) - (1 - e i) * (1 - e k) := by
    have := he.ortho hik
    linear_combination this
  apply x.2.ne_top
  rw [Ideal.eq_top_iff_one, h1]
  apply x.asIdeal.sub_mem (x.asIdeal.add_mem hx hx') (x.asIdeal.mul_mem_left _ hx')
noncomputable abbrev cover (he : CompleteOrthogonalIdempotents e) : (Spec (CommRingCat.of S)).OpenCover :=
  Scheme.Cover.mkOfCovers ι (fun i => Spec (CommRingCat.of (S ⧸ Ideal.span {1 - e i}))) (chart e)
    (covers e he) (fun i => isOpenImmersion_chart e he i)
/--
[AlgebraicGeometry_existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_specMap_quotient_mk_comp_eq_of_completeOrthogonalIdempotents.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
  {ι : Type} [Fintype ι] (e : ι → S) (he : CompleteOrthogonalIdempotents e)
  {N : (Scheme : Type (u + 1))} (gN : N ⟶ Spec (CommRingCat.of R))
  (φ : ∀ i : ι, Spec (CommRingCat.of (S ⧸ Ideal.span {1 - e i})) ⟶ N)
  (hφ : ∀ i, φ i ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R (S ⧸ Ideal.span {1 - e i})))) :
  ∃! Φ : Spec (CommRingCat.of S) ⟶ N, Φ ≫ gN = Spec.map (CommRingCat.ofHom (algebraMap R S)) ∧
    ∀ i, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {1 - e i}))) ≫ Φ = φ i := by
  classical
  have hcompat : ∀ i k : ι, pullback.fst ((cover e he).f i) ((cover e he).f k) ≫ φ i =
      pullback.snd ((cover e he).f i) ((cover e he).f k) ≫ φ k := by
    intro i k
    if hik : i = k then
      subst hik
      rw [fst_eq_snd_of_mono_eq]
    else
      let _ : IsEmpty ↥(pullback ((cover e he).f i) ((cover e he).f k)) :=
        Scheme.isEmpty_pullback_iff.mpr (disjoint_range_chart e he hik)
      apply Limits.IsInitial.hom_ext isInitialOfIsEmpty _ _
  have hglue : ∀ i : ι, chart e i ≫ (cover e he).glueMorphisms φ hcompat = φ i :=
    fun i => Scheme.Cover.ι_glueMorphisms (cover e he) φ hcompat i
  refine ⟨(cover e he).glueMorphisms φ hcompat, ⟨?_, fun i => hglue i⟩, ?_⟩
  ·
    apply Scheme.Cover.hom_ext (cover e he)
    intro i
    change chart e i ≫ _ ≫ gN = chart e i ≫ _
    rw [← Category.assoc, hglue, hφ, ← Spec.map_comp]
    rfl
  ·
    rintro Φ' ⟨-, hΦ'⟩
    apply Scheme.Cover.hom_ext (cover e he)
    intro i
    change chart e i ≫ Φ' = chart e i ≫ _
    rw [hglue]
    apply hΦ' i


-- created on 2026-10-20
