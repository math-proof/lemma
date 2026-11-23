module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Instance.AlgebraicGeometry_ProjSpace
public import Structure.AlgebraicGeometry_ProjSpace
public import Notation.AlgebraicGeometry_ProjSpace

public noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section PnSetup

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace


public theorem irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal
      ≤ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → MvPolynomial _ R)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi f hf
  have hf' : f.IsHomogeneous i := (MvPolynomial.mem_homogeneousSubmodule i f).mp hf
  show f ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R
  rw [← pow_one (MvPolynomial.idealOfVars _ R), MvPolynomial.mem_pow_idealOfVars_iff]
  intro x hx
  rw [MvPolynomial.mem_support_iff] at hx
  have hdeg : Finsupp.degree x = i := by
    rw [Finsupp.degree_eq_weight_one]; exact hf' hx
  omega

end StdCover

section Setup

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace


public theorem X_mem_one (j : Fin (n + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ∈ 𝒜 1 :=
  (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)


public theorem awayι_comp_π (i : Fin (n + 1)) :
    Proj.awayι 𝒜 (MvPolynomial.X i) (X_mem_one R n i) one_pos
      ≫ π R n
      = Spec.map (CommRingCat.ofHom (algebraMap R (Away 𝒜 (MvPolynomial.X i)))) := by
  unfold π
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl


public theorem ratio_self (i : Fin (n + 1)) :
    ratio R n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio, Away.val_mk, HomogeneousLocalization.val_one,
    ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩


public theorem val_algebraMap (i : Fin (n + 1)) (r : R) :
    (algebraMap R (Away 𝒜 (MvPolynomial.X i)) r).val
      = algebraMap (MvPolynomial (Fin (n + 1)) R) _ (MvPolynomial.C r) := by
  rfl

end Setup

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace


public theorem affineOpenCover_f (j : Fin (n + 1)) :
    (affineOpenCover R n).openCover.f j
      = Proj.awayι 𝒜 (MvPolynomial.X j) (X_mem_one R n j) one_pos := rfl

end StdCover

section AdjoinRatio

variable (R : Type u) [CommRing R] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace


public theorem awayMk_monomial (i : Fin (n + 1)) (d : ℕ)
    (e : Fin (n + 1) →₀ ℕ) (hd : e.degree = d) (r : R)
    (hm : MvPolynomial.monomial e r ∈ 𝒜 (d • 1)) :
    Away.mk 𝒜 (X_mem_one R n i) d (MvPolynomial.monomial e r) hm
      = algebraMap R _ r * ∏ j, (ratio R n i j) ^ (e j) := by
  have hdsum : ∑ j, e j = d := by
    rw [← hd, Finsupp.degree]
    exact (Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => Finsupp.notMem_support_iff.mp hj)).symm
  apply HomogeneousLocalization.val_injective
  have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
      = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
  rw [hval, map_mul, map_prod]
  simp only [map_pow, ratio, ← hval, Away.val_mk,
    val_algebraMap, Localization.mk_pow,
    ← Localization.mk_one_eq_algebraMap, Localization.mk_prod, Localization.mk_mul]
  congr 1
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_pow]
  · refine Subtype.ext ?_
    push_cast
    simp only [Finset.prod_pow_eq_pow_sum, pow_one, one_mul, hdsum]


public theorem adjoin_range_ratio (i : Fin (n + 1)) :
    Algebra.adjoin R (Set.range (ratio R n i)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective 𝒜 (X_mem_one R n i) z
  have ha' : a.IsHomogeneous d := (mem_homogeneousSubmodule d a).mp (by simpa using ha)

  have hdeg : ∀ e ∈ a.support, (e : Fin (n + 1) →₀ ℕ).degree = d := fun e he => by
    rw [Finsupp.degree_eq_weight_one]; exact ha' (MvPolynomial.mem_support_iff.mp he)
  have hsum : Away.mk 𝒜 (X_mem_one R n i) d a ha
      = ∑ e ∈ a.support.attach,
          Away.mk 𝒜 (X_mem_one R n i) d
            (MvPolynomial.monomial e.1 (a.coeff e.1))
            ((mem_homogeneousSubmodule _ _).mpr
              (isHomogeneous_monomial _
                (by simp only [smul_eq_mul, mul_one]; exact hdeg e.1 e.2))) := by
    apply HomogeneousLocalization.val_injective
    have hval : (HomogeneousLocalization.val : Away 𝒜 (X i) → Localization.Away (X i))
        = (algebraMap (Away 𝒜 (X i)) (Localization.Away (X i))) := rfl
    rw [hval, map_sum]
    simp only [← hval, Away.val_mk]
    rw [Finset.sum_attach a.support
      (fun e => Localization.mk (monomial e (a.coeff e))
        (⟨(X i)^d, Away.val_mk._proof_1 d⟩ :
          Submonoid.powers (X i : MvPolynomial (Fin (n+1)) R))),
      ← Localization.mk_sum]
    congr 1
    exact MvPolynomial.as_sum a
  rw [hsum]
  refine Subalgebra.sum_mem _ fun e _ => ?_
  rw [awayMk_monomial R n i d e.1 (hdeg e.1 e.2) (a.coeff e.1)]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.prod_mem _ fun j _ =>
      Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _)

end AdjoinRatio

section ProdOver

variable (R : Type u) [CommRing R]


public theorem isProper_prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    IsProper (prodOverπ R e) := by
  induction m with
  | zero => exact inferInstanceAs (IsProper (𝟙 _))
  | succ m ih =>
    haveI := ih (e ∘ Fin.succ)
    change IsProper (pullback.fst _ _ ≫ π R (e 0))
    infer_instance


public theorem prodPr_comp_π {m : ℕ} (e : Fin m → ℕ) (k : Fin m) :
    prodPr R e k ≫ π R (e k) = prodOverπ R e := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    match k with
    | ⟨0, _⟩ => rfl
    | ⟨k + 1, hk⟩ =>
      have key := ih (e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩
      calc (pullback.snd _ _ ≫
            prodPr R (e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩)
              ≫ π R (e ⟨k + 1, hk⟩)
          = pullback.snd _ _ ≫ (prodPr R (e ∘ Fin.succ)
              ⟨k, Nat.succ_lt_succ_iff.mp hk⟩ ≫
              π R ((e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩)) :=
            Category.assoc _ _ _
        _ = pullback.snd _ _ ≫ prodOverπ R (e ∘ Fin.succ) := by rw [key]
        _ = prodOverπ R e := (pullback.condition).symm


public theorem prodLift_comp_prodOverπ {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    {m : ℕ} (e : Fin m → ℕ)
    (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
    (hg : ∀ k, g k ≫ π R (e k) = s) :
    prodLift R s e g hg ≫ prodOverπ R e = s := by
  exact (prodLiftAux R s e g hg).2


public theorem prodLift_comp_prodPr {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    {m : ℕ} (e : Fin m → ℕ)
    (g : ∀ k, X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (e k + 1)) R))
    (hg : ∀ k, g k ≫ π R (e k) = s) (k : Fin m) :
    prodLift R s e g hg ≫ prodPr R e k = g k := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    match k with
    | ⟨0, _⟩ => exact pullback.lift_fst _ _ _
    | ⟨k + 1, hk⟩ =>
      show (pullback.lift _ _ _) ≫ (pullback.snd _ _ ≫
        prodPr R (e ∘ Fin.succ) ⟨k, Nat.succ_lt_succ_iff.mp hk⟩) = _
      rw [← Category.assoc, pullback.lift_snd]
      exact ih (e ∘ Fin.succ) (fun k => g k.succ) (fun k => hg k.succ)
        ⟨k, Nat.succ_lt_succ_iff.mp hk⟩

end ProdOver

section MapGraded

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)

open scoped AlgebraicGeometry_ProjSpace


public theorem mvMapGraded_X (j : Fin (n + 1)) :
    (mvMapGraded R A n) (MvPolynomial.X j) = MvPolynomial.X j :=
  MvPolynomial.map_X _ j


public theorem irrelevant_le_map_mvMapGraded :
    (HomogeneousIdeal.irrelevant 𝒜A)
      ≤ HomogeneousIdeal.map (mvMapGraded R A n)
          (HomogeneousIdeal.irrelevant 𝒜R) := by
  intro a ha
  show a ∈ (HomogeneousIdeal.map (mvMapGraded R A n)
    (HomogeneousIdeal.irrelevant _)).toIdeal
  rw [HomogeneousIdeal.toIdeal_map, MvPolynomial.as_sum a]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rintro rfl
    refine (MvPolynomial.mem_support_iff.mp hd) ?_
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at ha
    classical
    conv_lhs => rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (n + 1)) A) a]
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [ha, coeff_zero]
    · exact ((mem_homogeneousSubmodule i _).mp
        (DirectSum.decompose (homogeneousSubmodule (Fin (n + 1)) A) a i).2).coeff_eq_zero
        (by simpa [Finsupp.degree] using hi0.symm)
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr (Finsupp.support_eq_empty.not.mpr hd0)
  obtain ⟨q, hq⟩ : (X j : MvPolynomial (Fin (n + 1)) A) ∣ monomial d (coeff d a) :=
    X_dvd_monomial.mpr (Or.inr (Finsupp.mem_support_iff.mp hj))
  rw [hq, show (X j : MvPolynomial (Fin (n + 1)) A)
      = (mvMapGraded R A n).toRingHom (X j) from (map_X _ j).symm]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
    ((HomogeneousIdeal.mem_irrelevant_iff _ _).mpr (by
      rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _
        ((mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X R j)) one_ne_zero])))


public theorem map_eq : map R A n = Proj.map (mvMapGraded R A n) (irrelevant_le_map_mvMapGraded R A n) := rfl

end MapGraded

end ProjSpace

section Carrier

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))


end Carrier

section CarrierProj

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))


end CarrierProj

end AlgebraicGeometry

end
