import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.ResidueFieldFunctor
open Polynomial IsLocalRing IntermediateField in


/--
[aeval_eq_eval_residue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma aeval_eq_eval_residue
  [CommRing A]
  [IsLocalRing A]
  [HenselianLocalRing A]
  {p : (ResidueField A)[X]}
  {x : ResidueField A} :
-- imply
  aeval x p = eval x p := by
-- proof
  simp [aeval_def]

/--
[hensel_root_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma hensel_root_lift
  [CommRing A]
  [IsLocalRing A]
  [HenselianLocalRing A]
  {f : A[X]}
  {a₀ : ResidueField A}
-- given
  (hf : f.Monic)
  (hsep : (f.map (residue A)).Separable)
  (ha₀ : (f.map (residue A)).IsRoot a₀) :
-- imply
  ∃ a : A, f.IsRoot a ∧ residue A a = a₀ := by
-- proof
  have hensel := ((HenselianLocalRing.TFAE (R := A)).out 0 1).mp ‹HenselianLocalRing A›
  have h1 : aeval a₀ f = 0 := by
    have : aeval a₀ f = eval a₀ (map (residue A) f) := by
      simp [aeval_def, eval_map, ResidueField.algebraMap_eq]
    rw [this]; exact ha₀
  have h2 : aeval a₀ (derivative f) ≠ 0 := by
    have key : aeval a₀ (derivative f) = eval a₀ (derivative (map (residue A) f)) := by
      show eval₂ (algebraMap A _) a₀ (derivative f) = _
      rw [ResidueField.algebraMap_eq]
      conv_rhs => rw [Polynomial.derivative_map]
      rw [eval_map]
    rw [key]
    have hroot : aeval a₀ (map (residue A) f) = 0 := by
      rw [aeval_eq_eval_residue]; exact ha₀
    have := hsep.aeval_derivative_ne_zero hroot
    rwa [aeval_eq_eval_residue] at this
  exact hensel f hf a₀ h1 h2

/--
[root_maps_to_residue_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma root_maps_to_residue_root
  [CommRing A]
  [IsLocalRing A]
  [HenselianLocalRing A]
  {f : A[X]}
  {a : A}
-- given
  (ha : f.IsRoot a) :
-- imply
  (f.map (residue A)).IsRoot (residue A a) := by
-- proof
  simp only [IsRoot, eval_map]
  rw [eval₂_at_apply, ha, map_zero]

/--
[hensel_root_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma hensel_root_injective
  [CommRing A]
  [IsLocalRing A]
  [HenselianLocalRing A]
  {f : A[X]}
  {a b : A}
-- given
  (hf : f.Monic)
  (hsep : (f.map (residue A)).Separable)
  (ha : f.IsRoot a)
  (hb : f.IsRoot b)
  (hab : residue A a = residue A b) :
-- imply
  a = b := by
-- proof
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha
  have hfb : (b - a) * q.eval b = 0 := by
    have := hb; rw [IsRoot, hq, eval_mul, eval_sub, eval_X, eval_C] at this; exact this
  have hqa : f.derivative.eval a = q.eval a := by
    have hd : f.derivative = (X - C a) * q.derivative + q := by
      rw [hq, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]; ring
    rw [hd, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, zero_add]
  have hderiv : IsUnit (f.derivative.eval a) := by
    rw [← notMem_maximalIdeal]
    intro hmem_deriv
    have h1 : (residue A) (f.derivative.eval a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem_deriv
    have h2 : (residue A) (f.derivative.eval a) =
      eval (residue A a) (derivative (map (residue A) f)) := by
      rw [show (residue A) (f.derivative.eval a) =
        (f.derivative.map (residue A)).eval (residue A a) from by rw [eval_map, eval₂_at_apply]]
      rw [Polynomial.derivative_map]
    rw [h2] at h1
    have hroot : aeval (residue A a) (map (residue A) f) = 0 := by
      rw [aeval_eq_eval_residue]; exact root_maps_to_residue_root ha
    have := hsep.aeval_derivative_ne_zero hroot
    rw [aeval_eq_eval_residue] at this
    exact this h1
  have hqa_unit : IsUnit (q.eval a) := hqa ▸ hderiv
  have hres_q : residue A (q.eval a) = residue A (q.eval b) := by
    rw [show residue A (q.eval a) = (q.map (residue A)).eval (residue A a) from by
      rw [eval_map, eval₂_at_apply]]
    rw [show residue A (q.eval b) = (q.map (residue A)).eval (residue A b) from by
      rw [eval_map, eval₂_at_apply]]
    rw [hab]
  have hqb_unit : IsUnit (q.eval b) := by
    rw [← notMem_maximalIdeal]
    intro hmem_qb
    have h1 : residue A (q.eval b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem_qb
    rw [← hres_q] at h1
    exact (hqa_unit.map (residue A)).ne_zero h1
  have hab_zero : b - a = 0 := by rwa [hqb_unit.mul_left_eq_zero] at hfb
  exact (eq_of_sub_eq_zero hab_zero).symm
end HenselRootBijection

/--
[adjoinRoot_isLocalRing_of_irred_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_isLocalRing_of_irred_map
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
  [IsDomain (AdjoinRoot g)]
  [Module.Finite A (AdjoinRoot g)]
-- given
  (hg_monic : g.Monic)
  (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
-- imply
  IsLocalRing (AdjoinRoot g) := by
-- proof
  set B := AdjoinRoot g
  set J := Ideal.map (AdjoinRoot.of g) (maximalIdeal A) with hJ_def
  have e : B ⧸ J ≃+* (ResidueField A)[X] ⧸
    Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))} :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal A) g
  have hmax_span : (Ideal.span ({g.map (Ideal.Quotient.mk (maximalIdeal A))} :
    Set ((ResidueField A)[X]))).IsMaximal :=
    @AdjoinRoot.span_maximal_of_irreducible (ResidueField A) _ _ ⟨hg_irred_map⟩
  have hfield_quot : IsField ((ResidueField A)[X] ⧸
    Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))}) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax_span
  have hfield_BJ : IsField (B ⧸ J) := e.toMulEquiv.isField hfield_quot
  have hJ_max : J.IsMaximal := Ideal.Quotient.maximal_of_isField J hfield_BJ
  apply IsLocalRing.of_unique_max_ideal
  exact ⟨J, hJ_max, fun M hM => by
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    haveI : M.IsMaximal := hM
    have hcomap_max := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) (S := B) M
    have hcomap_eq := IsLocalRing.eq_maximalIdeal hcomap_max
    have h_le : maximalIdeal A ≤ Ideal.comap (algebraMap A B) M := hcomap_eq ▸ le_refl _
    have hJ_le_M : J ≤ M := Ideal.map_le_iff_le_comap.mpr h_le
    exact (hJ_max.eq_of_le hM.ne_top hJ_le_M).symm⟩

/--
[adjoinRoot_of_injective_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_of_injective_of_monic
  [CommRing A]
  [IsDomain A]
  {g : Polynomial A}
-- given
  (hg : g.Monic)
  (hdeg : 0 < g.natDegree) :
-- imply
  Function.Injective (AdjoinRoot.of g) := by
-- proof
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro a ha
  rw [RingHom.mem_ker] at ha
  change AdjoinRoot.mk g (Polynomial.C a) = 0 at ha
  rw [AdjoinRoot.mk_eq_zero] at ha
  obtain ⟨q, hq⟩ := ha
  by_cases ha0 : a = 0
  · simp [ha0]
  · exfalso
    have hCa_ne : Polynomial.C a ≠ 0 := Polynomial.C_ne_zero.mpr ha0
    have hq_ne : q ≠ 0 := by intro hq0; rw [hq0, mul_zero] at hq; exact hCa_ne hq
    have h2 : (g * q).natDegree = g.natDegree + q.natDegree :=
      Polynomial.natDegree_mul hg.ne_zero hq_ne
    rw [← hq] at h2
    have : (Polynomial.C a).natDegree = 0 := Polynomial.natDegree_C a
    omega

/--
[natDegree_pos_of_monic_irred_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma natDegree_pos_of_monic_irred_map
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
-- given
  (hg_monic : g.Monic)
  (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (maximalIdeal A)))) :
-- imply
  0 < g.natDegree := by
-- proof
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  have hd0 : g.natDegree = 0 := h
  have hg1 : g = 1 := Polynomial.eq_one_of_monic_natDegree_zero hg_monic hd0
  rw [hg1, Polynomial.map_one] at hg_irred_map
  exact not_irreducible_one hg_irred_map

/--
[adjoinRoot_map_maximalIdeal_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_map_maximalIdeal_isMaximal
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
  [IsDomain (AdjoinRoot g)]
-- given
  (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (maximalIdeal A)))) :
-- imply
  (Ideal.map (AdjoinRoot.of g) (maximalIdeal A)).IsMaximal := by
-- proof
  set B := AdjoinRoot g
  set J := Ideal.map (AdjoinRoot.of g) (maximalIdeal A)
  have e : B ⧸ J ≃+* (ResidueField A)[X] ⧸
    Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))} :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal A) g
  have hmax_span : (Ideal.span ({g.map (Ideal.Quotient.mk (maximalIdeal A))} :
    Set ((ResidueField A)[X]))).IsMaximal :=
    @AdjoinRoot.span_maximal_of_irreducible (ResidueField A) _ _ ⟨hg_irred_map⟩
  exact Ideal.Quotient.maximal_of_isField J
    (e.toMulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax_span))

/--
[adjoinRoot_isDVR_of_irred_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_isDVR_of_irred_map
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
  [IsDomain (AdjoinRoot g)]
  [Module.Finite A (AdjoinRoot g)]
  [IsLocalRing (AdjoinRoot g)]
-- given
  (hg_monic : g.Monic)
  (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
-- imply
  IsDiscreteValuationRing (AdjoinRoot g) := by
-- proof
  set B := AdjoinRoot g
  haveI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hnotfield : ¬ IsField B := by
    intro hfield
    have hdeg := natDegree_pos_of_monic_irred_map hg_monic hg_irred_map
    have hinj := adjoinRoot_of_injective_of_monic hg_monic hdeg
    haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hinj hfield)
  have hJ_max := adjoinRoot_map_maximalIdeal_isMaximal A g hg_irred_map
  have h_max_eq : maximalIdeal B = Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    (IsLocalRing.eq_maximalIdeal hJ_max).symm
  have hprinc : Submodule.IsPrincipal (maximalIdeal B) := h_max_eq ▸ inferInstance
  exact ((IsDiscreteValuationRing.TFAE B hnotfield).out 4 0).mp hprinc

/--
[adjoinRoot_isLocalHom_of_irred_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_isLocalHom_of_irred_map
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
  [IsDomain (AdjoinRoot g)]
  [Module.Finite A (AdjoinRoot g)]
  [IsLocalRing (AdjoinRoot g)]
-- given
  (hg_monic : g.Monic)
  (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
-- imply
  IsLocalHom (AdjoinRoot.of g) := by
-- proof
  apply ((local_hom_TFAE (AdjoinRoot.of g)).out 3 0).mp
  have hJ_max := adjoinRoot_map_maximalIdeal_isMaximal A g hg_irred_map
  have h_max_eq : maximalIdeal (AdjoinRoot g) =
    Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    (IsLocalRing.eq_maximalIdeal hJ_max).symm
  rwa [h_max_eq]

/--
[adjoinRoot_maxIdeal_eq_map_of_irred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_maxIdeal_eq_map_of_irred
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
  [IsDomain (AdjoinRoot g)]
  [Module.Finite A (AdjoinRoot g)]
  [IsLocalRing (AdjoinRoot g)]
-- given
  (hg_monic : g.Monic)
  (hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
-- imply
  IsLocalRing.maximalIdeal (AdjoinRoot g) = Ideal.map (AdjoinRoot.of g) (IsLocalRing.maximalIdeal A) := by
-- proof
  exact (IsLocalRing.eq_maximalIdeal
    (adjoinRoot_map_maximalIdeal_isMaximal A g hg_irred_map)).symm

/--
[adjoinRoot_dvr_of_irreducible_lift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_dvr_of_irreducible_lift
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
  {gbar : (ResidueField A)[X]}
-- given
  (hgbar_monic : gbar.Monic)
  (hgbar_irred : Irreducible gbar)
  (hgbar_sep : gbar.Separable) :
-- imply
  ∃ (g : Polynomial A) (_ : g.Monic) (_ : g.map (residue A) = gbar) (_ : IsDomain (AdjoinRoot g)) (_ : IsDiscreteValuationRing (AdjoinRoot g)) (_ : IsLocalHom (AdjoinRoot.of g)) (_ : Module.Finite A (AdjoinRoot g)), ∃ (hAlg : Algebra (ResidueField A) (ResidueField (AdjoinRoot g))) (_ : @FiniteDimensional (ResidueField A) (ResidueField (AdjoinRoot g)) _ _ hAlg.toModule) (_ : @Algebra.IsSeparable (ResidueField A) (ResidueField (AdjoinRoot g)) _ _ hAlg), Nonempty (ResidueField (AdjoinRoot g) ≃+* AdjoinRoot gbar) := by
-- proof
  have hlift : gbar ∈ lifts (residue A) :=
    (lifts_iff_coeff_lifts gbar).mpr (fun n => residue_surjective (gbar.coeff n))
  obtain ⟨g, hmap, hg_deg, hg_monic⟩ := lifts_and_natDegree_eq_and_monic hlift hgbar_monic
  have hgbar_ne : gbar ≠ 0 := hgbar_irred.ne_zero
  have hg_irred_map : Irreducible (g.map (Ideal.Quotient.mk (maximalIdeal A))) :=
    hmap ▸ hgbar_irred
  have hg_irred : Irreducible g :=
    Polynomial.Monic.irreducible_of_irreducible_map
      (Ideal.Quotient.mk (maximalIdeal A)) g hg_monic hg_irred_map
  have hg_prime : Prime g := UniqueFactorizationMonoid.irreducible_iff_prime.mp hg_irred
  haveI hdom : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hg_prime
  haveI hfin : Module.Finite A (AdjoinRoot g) := hg_monic.finite_adjoinRoot
  haveI : IsLocalRing (AdjoinRoot g) :=
    adjoinRoot_isLocalRing_of_irred_map A g hg_monic hg_irred_map
  have hDVR : IsDiscreteValuationRing (AdjoinRoot g) :=
    adjoinRoot_isDVR_of_irred_map A g hg_monic hg_irred_map
  have hLH : IsLocalHom (AdjoinRoot.of g) :=
    adjoinRoot_isLocalHom_of_irred_map A g hg_monic hg_irred_map
  have h_max_eq : maximalIdeal (AdjoinRoot g) =
    Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    adjoinRoot_maxIdeal_eq_map_of_irred A g hg_monic hg_irred_map
  set B := AdjoinRoot g
  have e1 : B ⧸ maximalIdeal B ≃+* B ⧸ Ideal.map (AdjoinRoot.of g) (maximalIdeal A) :=
    Ideal.quotEquivOfEq h_max_eq
  have e2 : (B ⧸ Ideal.map (AdjoinRoot.of g) (maximalIdeal A)) ≃+*
    (Polynomial (ResidueField A) ⧸
      Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))}) :=
    (AdjoinRoot.quotientIso A g).toRingEquiv
  have e3 : (Polynomial (ResidueField A) ⧸
    Ideal.span {g.map (Ideal.Quotient.mk (maximalIdeal A))}) ≃+*
    AdjoinRoot gbar :=
    Ideal.quotEquivOfEq (congr_arg (fun p => Ideal.span {p}) hmap)
  have iso : ResidueField B ≃+* AdjoinRoot gbar := e1.trans (e2.trans e3)
  set k := ResidueField A
  haveI : Fact (Irreducible gbar) := ⟨hgbar_irred⟩
  let algMap_k_adjgbar : k →+* AdjoinRoot gbar :=
    (AdjoinRoot.mk gbar).comp (Polynomial.C)
  let hAlg : Algebra k (ResidueField B) :=
    RingHom.toAlgebra (iso.symm.toRingHom.comp algMap_k_adjgbar)
  have hFD : @FiniteDimensional k (ResidueField B) _ _ hAlg.toModule := by
    have algEquiv : @AlgEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _ :=
      @AlgEquiv.ofRingEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _
        (f := iso) (fun x => by
          show iso (iso.symm ((algebraMap k (AdjoinRoot gbar)) x)) =
            (algebraMap k (AdjoinRoot gbar)) x
          simp)
    haveI : Module.Finite k (AdjoinRoot gbar) :=
      (AdjoinRoot.powerBasis hgbar_ne).finite
    exact @Module.Finite.equiv k (AdjoinRoot gbar) (ResidueField B) _
      inferInstance inferInstance inferInstance hAlg.toModule _
      algEquiv.symm.toLinearEquiv
  haveI hSep_adj : Algebra.IsSeparable k (AdjoinRoot gbar) := by
    open IntermediateField in
    have hSepRoot : IsSeparable k (AdjoinRoot.root gbar) := by
      unfold IsSeparable
      rw [AdjoinRoot.minpoly_root hgbar_ne]
      simp [hgbar_monic.leadingCoeff]
      exact hgbar_sep
    haveI : Algebra.IsSeparable k ↥k⟮AdjoinRoot.root gbar⟯ :=
      (isSeparable_adjoin_simple_iff_isSeparable k (AdjoinRoot gbar)).mpr hSepRoot
    exact Algebra.IsSeparable.of_algHom k (↥k⟮AdjoinRoot.root gbar⟯)
      ((IntermediateField.equivOfEq (IntermediateField.adjoin_root_eq_top gbar)).trans
        IntermediateField.topEquiv).symm.toAlgHom
  have hSep : @Algebra.IsSeparable k (ResidueField B) _ _ hAlg := by
    have algEquiv : @AlgEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _ :=
      @AlgEquiv.ofRingEquiv k (ResidueField B) (AdjoinRoot gbar) _ _ _ hAlg _
        (f := iso) (fun x => by
          show iso (iso.symm ((algebraMap k (AdjoinRoot gbar)) x)) =
            (algebraMap k (AdjoinRoot gbar)) x
          simp)
    exact @Algebra.IsSeparable.of_algHom k _ (ResidueField B) (AdjoinRoot gbar)
      _ _ hAlg _ algEquiv.toAlgHom _
  exact ⟨g, hg_monic, hmap, hdom, hDVR, hLH, hfin, hAlg, hFD, hSep, ⟨iso⟩⟩

/--
[henselian_dvr_extension_of_henselian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma henselian_dvr_extension_of_henselian
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [IsAdicComplete (maximalIdeal B) B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B] :
-- imply
  HenselianLocalRing B := by
-- proof
  exact ((HenselianLocalRing.TFAE B).out 1 0).mp <| by
    open Polynomial in
    intro f hf a₀ hroot hderiv
    set fbar := f.map (IsLocalRing.residue B) with hfbar_def
    have hroot' : fbar.IsRoot a₀ := by
      simp only [IsRoot, hfbar_def, eval_map]
      rwa [aeval_def, IsLocalRing.ResidueField.algebraMap_eq] at hroot
    have hderiv' : fbar.derivative.eval a₀ ≠ 0 := by
      simp only [hfbar_def, derivative_map, eval_map]
      intro heq; apply hderiv
      rwa [aeval_def, IsLocalRing.ResidueField.algebraMap_eq]
    set qbar := fbar /ₘ (X - C a₀)
    have hfbar_factor : fbar = (X - C a₀) * qbar :=
      (mul_divByMonic_eq_iff_isRoot.mpr hroot').symm
    have hcoprime : IsCoprime (X - C a₀) qbar :=
      isCoprime_of_is_root_of_eval_derivative_ne_zero fbar a₀ hderiv'
    have hfbar_factor' : map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) f =
      (X - C a₀) * qbar := by convert hfbar_factor using 1
    obtain ⟨g, h, hfgh, hg_map, _, hg_deg⟩ :=
      hensel_lemma_III f (X - C a₀) qbar hfbar_factor' hcoprime
    have hg_natdeg : g.natDegree = 1 := by
      rw [hg_deg]; exact natDegree_X_sub_C a₀
    have hcoeff1 : (Ideal.Quotient.mk (maximalIdeal B)) (g.coeff 1) = 1 := by
      have := congr_arg (fun p => p.coeff 1) hg_map
      simp only [coeff_map] at this; rw [this]
      change (X - C a₀ : (ResidueField B)[X]).coeff 1 = 1
      simp [coeff_sub, coeff_X]
    have hcoeff0 : (Ideal.Quotient.mk (maximalIdeal B)) (g.coeff 0) = -a₀ := by
      have := congr_arg (fun p => p.coeff 0) hg_map
      simp only [coeff_map] at this; rw [this]
      change (X - C a₀ : (ResidueField B)[X]).coeff 0 = -a₀
      simp [coeff_sub, coeff_X, coeff_C]
    have hlc_unit : IsUnit g.leadingCoeff := by
      apply isUnit_of_map_unit (IsLocalRing.residue B)
      change IsUnit ((Ideal.Quotient.mk (maximalIdeal B)) g.leadingCoeff)
      rw [Polynomial.leadingCoeff, hg_natdeg, hcoeff1]; exact isUnit_one
    obtain ⟨u, hu_eq⟩ := hlc_unit
    set a := -(g.coeff 0) * (↑u⁻¹ : B) with ha_def
    have hga : g.IsRoot a := by
      rw [IsRoot]
      have key : g.eval a = g.leadingCoeff * a + g.coeff 0 := by
        rw [Polynomial.eval_eq_sum_range' (n := 2) (by omega)]
        simp [Finset.sum_range_succ, pow_zero, pow_one, leadingCoeff, hg_natdeg]; ring
      rw [key, ← hu_eq, ha_def]
      have huinv : (u : B) * (↑u⁻¹ : B) = 1 := Units.mul_inv u
      calc (↑u : B) * (-(g.coeff 0) * ↑u⁻¹) + g.coeff 0
        = -(↑u * ↑u⁻¹ * g.coeff 0) + g.coeff 0 := by ring
        _ = -(1 * g.coeff 0) + g.coeff 0 := by rw [huinv]
        _ = 0 := by ring
    have hfa : f.IsRoot a := by
      rw [IsRoot, hfgh, eval_mul, show eval a g = 0 from hga, zero_mul]
    have ha_res : IsLocalRing.residue B a = a₀ := by
      show (Ideal.Quotient.mk (maximalIdeal B)) a = a₀
      rw [ha_def, map_mul, map_neg, hcoeff0]
      have hphi_uinv : (Ideal.Quotient.mk (maximalIdeal B)) (↑u⁻¹ : B) = 1 := by
        have hu_map : (Ideal.Quotient.mk (maximalIdeal B)) (↑u : B) = 1 := by
          rw [hu_eq, Polynomial.leadingCoeff, hg_natdeg]; exact hcoeff1
        have h := congr_arg (· * (Ideal.Quotient.mk (maximalIdeal B)) (↑u⁻¹ : B)) hu_map
        simp only [one_mul] at h; rw [← h, ← map_mul,
          show (↑u : B) * (↑u⁻¹ : B) = 1 from Units.mul_inv u, map_one]
      rw [hphi_uinv, mul_one]
      exact neg_neg a₀
    exact ⟨a, hfa, ha_res⟩

/--
[finiteDimensional_residueField_of_finite_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma finiteDimensional_residueField_of_finite_dvr
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B] :
-- imply
  FiniteDimensional (ResidueField A) (ResidueField B) := by
-- proof
  letI σ := IsLocalRing.residue A
  haveI : RingHomSurjective σ := ⟨Ideal.Quotient.mk_surjective⟩
  have hcompat : ∀ a : A, (IsLocalRing.residue B) ((algebraMap A B) a) =
    (algebraMap (ResidueField A) (ResidueField B)) ((IsLocalRing.residue A) a) :=
    fun a => RingHom.congr_fun (IsLocalRing.ResidueField.map_comp_residue (algebraMap A B)).symm a
  let f : B →ₛₗ[σ] ResidueField B := {
    toFun := IsLocalRing.residue B
    map_add' := map_add _
    map_smul' := fun a b => by
      simp only [σ, Algebra.smul_def, map_mul]
      rw [hcompat a]
  }
  exact Module.Finite.of_surjective f Ideal.Quotient.mk_surjective

/--
[adjoinRoot_module_finite_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_module_finite_of_monic
  [CommRing A]
  {g : Polynomial A}
-- given
  (hg : g.Monic) :
-- imply
  Module.Finite A (AdjoinRoot g) :=
-- proof
  hg.finite_adjoinRoot

/--
[adjoinRoot_isDomain_of_irreducible_mod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_isDomain_of_irreducible_mod
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {g : Polynomial A}
-- given
  (hg : g.Monic)
  (hirr : Irreducible (g.map (residue A))) :
-- imply
  IsDomain (AdjoinRoot g) :=
-- proof
  AdjoinRoot.isDomain_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue A) g hg hirr))

/--
[finrank_adjoinRoot_of_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma finrank_adjoinRoot_of_monic
  [CommRing A]
  [IsDomain A]
  {g : Polynomial A}
-- given
  (hg : g.Monic) :
-- imply
  Module.finrank A (AdjoinRoot g) = g.natDegree := by
-- proof
  rw [(AdjoinRoot.powerBasis' hg).finrank, AdjoinRoot.powerBasis'_dim]

/--
[surjective_of_range_sup_maximalIdeal_smul_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma surjective_of_range_sup_maximalIdeal_smul_eq_top
  [CommRing A]
  [IsLocalRing A]
  [CommRing C]
  [Algebra A C]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  {φ : C →ₐ[A] B}
-- given
  (hsup : LinearMap.range φ.toLinearMap ⊔ IsLocalRing.maximalIdeal A • ⊤ = ⊤) :
-- imply
  Function.Surjective φ := by
-- proof
  intro b
  have hJ : IsLocalRing.maximalIdeal A ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have htop_le : (⊤ : Submodule A B) ≤ LinearMap.range φ.toLinearMap ⊔
    IsLocalRing.maximalIdeal A • ⊤ := le_of_eq hsup.symm
  have hle := @Submodule.le_of_le_smul_of_le_jacobson_bot A B _ _ _
    (IsLocalRing.maximalIdeal A) (LinearMap.range φ.toLinearMap) ⊤
    Module.Finite.fg_top hJ htop_le
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp (hle (Submodule.mem_top : b ∈ ⊤))
  exact ⟨c, hc⟩

/--
[injective_of_surjective_of_finrank_eq_of_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma injective_of_surjective_of_finrank_eq_of_domain
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing C]
  [IsDomain C]
  [Algebra A C]
  [Module.Finite A C]
  [CommRing B]
  [IsDomain B]
  [Algebra A B]
  [Module.Finite A B]
  {φ : C →ₐ[A] B}
-- given
  (hrank : Module.finrank A C = Module.finrank A B)
  (hsurj : Function.Surjective φ) :
-- imply
  Function.Injective φ := by
-- proof
  by_cases hinj_alg : Function.Injective (algebraMap A C)
  ·
    haveI : NoZeroSMulDivisors A C := by
      constructor
      intro a c hac
      simp only [Algebra.smul_def] at hac
      obtain ha | hc := mul_eq_zero.mp hac
      · left; exact hinj_alg (ha.trans (map_zero _).symm)
      · right; exact hc
    haveI : Module.IsTorsionFree A C := FaithfulSMul.to_isTorsionFree A C
    haveI : Module.Free A C := Module.free_of_finite_type_torsion_free' (R := A) (M := C)
    let K := LinearMap.ker φ.toLinearMap
    have hrn := Submodule.finrank_quotient_add_finrank K
    have hfq : Module.finrank A (C ⧸ K) = Module.finrank A B := by
      have e1 := LinearMap.quotKerEquivRange φ.toLinearMap
      rw [LinearMap.range_eq_top.mpr hsurj] at e1
      exact (e1.trans (Submodule.topEquiv (R := A) (M := B))).finrank_eq
    have hfk : Module.finrank A K = 0 := by omega
    haveI : Module.IsTorsionFree A K := by
      constructor
      intro r hr x y hxy
      exact Subtype.ext (Module.IsTorsionFree.isSMulRegular (M := C) hr (Subtype.ext_iff.mp hxy))
    haveI : Module.Free A K := Module.free_of_finite_type_torsion_free' (R := A) (M := K)
    have hK_bot : K = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx⟩ : K) = 0 :=
        ((Module.finrank_eq_zero_iff_of_free A K).mp hfk).eq_zero _
      simpa using this
    exact LinearMap.ker_eq_bot.mp hK_bot
  ·
    have hker_ne : RingHom.ker (algebraMap A C) ≠ ⊥ := by
      rwa [Ne, ← RingHom.injective_iff_ker_eq_bot]
    have hker_prime : (RingHom.ker (algebraMap A C)).IsPrime := RingHom.ker_isPrime _
    have hker_max : RingHom.ker (algebraMap A C) = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (hker_prime.isMaximal hker_ne)
    have hC_field : IsField C := by
      have hle : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A C) := hker_max ▸ le_refl _
      let hlift := fun a (ha : a ∈ IsLocalRing.maximalIdeal A) => RingHom.mem_ker.mp (hle ha)
      let f := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A C) hlift
      letI : Algebra (IsLocalRing.ResidueField A) C := f.toAlgebra
      haveI : IsScalarTower A (IsLocalRing.ResidueField A) C := by
        apply IsScalarTower.of_algebraMap_eq
        intro a
        exact (Ideal.Quotient.lift_mk _ _ hlift : f _ = _).symm
      haveI : Module.Finite (IsLocalRing.ResidueField A) C :=
        Module.Finite.of_restrictScalars_finite A _ C
      exact isField_of_isIntegral_of_isField' (Field.toIsField (IsLocalRing.ResidueField A))
    letI := hC_field.toField
    exact φ.toRingHom.injective
set_option maxHeartbeats 3200000 in

/--
[surjective_adjoinRoot_to_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma surjective_adjoinRoot_to_quotient
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B]
  [IsDomain B]
  [Algebra A B]
  [Module.Finite A B]
  {g : Polynomial A}
  {α : B}
-- given
  (hα_aeval : Polynomial.aeval α g = 0)
  (hg_monic : g.Monic)
  (hg_irr : Irreducible (g.map (IsLocalRing.residue A)))
  (hfinrank : Module.finrank A (AdjoinRoot g) = Module.finrank A B) :
-- imply
  Function.Surjective ((Ideal.Quotient.mk (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A))).comp (AdjoinRoot.liftHom g α hα_aeval).toRingHom) := by
-- proof
  haveI : Fact (Irreducible (g.map (IsLocalRing.residue A))) := ⟨hg_irr⟩
  set m := IsLocalRing.maximalIdeal A with hm_def
  set J := Ideal.map (algebraMap A B) m with hJ_def
  set q : B →+* B ⧸ J := Ideal.Quotient.mk J
  set phi := AdjoinRoot.liftHom g α hα_aeval
  have hkill : ∀ a ∈ m, (q.comp (algebraMap A B)) a = 0 := fun a ha => by
    show q (algebraMap A B a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_map_of_mem _ ha
  set algMap_k : IsLocalRing.ResidueField A →+* B ⧸ J :=
    Ideal.Quotient.lift m (q.comp (algebraMap A B)) hkill
  letI instAlg : Algebra (IsLocalRing.ResidueField A) (B ⧸ J) := algMap_k.toAlgebra
  haveI : IsScalarTower A (IsLocalRing.ResidueField A) (B ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algMap_k (IsLocalRing.residue A a) = algebraMap A (B ⧸ J) a
      exact (Ideal.Quotient.lift_mk _ _ _ : algMap_k _ = _)
  set gbar := g.map (IsLocalRing.residue A)
  have haeval : (Polynomial.aeval (R := IsLocalRing.ResidueField A) (A := B ⧸ J) (q α)) gbar = 0 := by
    simp only [Polynomial.aeval_def, gbar]
    rw [show (g.map (IsLocalRing.residue A)).eval₂
      (algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)) (q α) =
      g.eval₂ ((algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)).comp (IsLocalRing.residue A))
        (q α) from Polynomial.eval₂_map _ _ _]
    have hcomp : (algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)).comp
      (IsLocalRing.residue A) = q.comp (algebraMap A B) := by
      ext a; simp only [RingHom.comp_apply]; exact Ideal.Quotient.lift_mk _ _ _
    rw [hcomp, ← Polynomial.hom_eval₂ g (algebraMap A B) q α,
      show g.eval₂ (algebraMap A B) α = 0 from by rwa [← Polynomial.aeval_def], map_zero]
  set f := AdjoinRoot.liftHom gbar (q α) haeval
  haveI : Nontrivial (B ⧸ J) := by
    rw [Ideal.Quotient.nontrivial_iff]; intro hJ
    have h1 : (⊤ : Submodule A B) ≤ m • ⊤ := by
      rw [Ideal.smul_top_eq_map]; intro x _
      rw [Submodule.restrictScalars_mem]; change x ∈ J; rw [hJ]; trivial
    have h3 := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m ⊤
      Module.Finite.fg_top h1 (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    exact one_ne_zero (show (1 : B) = 0 by
      have := h3 ▸ (Submodule.mem_top : (1 : B) ∈ ⊤); rwa [Submodule.mem_bot] at this)
  have hf_inj : Function.Injective f := RingHom.injective f.toRingHom
  haveI : Module.Free A (AdjoinRoot g) :=
    Module.Free.of_basis (AdjoinRoot.isAdjoinRootMonic g hg_monic).powerBasis.basis
  have hndeg_pos : 0 < g.natDegree := by
    rw [← hg_monic.natDegree_map (IsLocalRing.residue A)]; exact hg_irr.natDegree_pos
  have hinj_alg : Function.Injective (algebraMap A B) := by
    by_contra h
    have hker : RingHom.ker (algebraMap A B) ≠ ⊥ := by
      rwa [Ne, ← RingHom.injective_iff_ker_eq_bot]
    obtain ⟨a, ha_mem, ha_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [RingHom.mem_ker] at ha_mem
    have : Module.finrank A B = 0 :=
      (Module.finrank_eq_zero_iff (R := A) (M := B)).mpr
        fun x => ⟨a, ha_ne, by simp [Algebra.smul_def, ha_mem]⟩
    linarith [(AdjoinRoot.isAdjoinRootMonic g hg_monic).finrank]
  haveI : NoZeroSMulDivisors A B := by
    constructor; intro a b hab; simp only [Algebra.smul_def] at hab
    obtain ha | hb := mul_eq_zero.mp hab
    · left; exact hinj_alg (ha.trans (map_zero _).symm)
    · right; exact hb
  haveI : Module.IsTorsionFree A B := FaithfulSMul.to_isTorsionFree A B
  haveI : Module.Free A B := Module.free_of_finite_type_torsion_free' (R := A) (M := B)
  haveI : FiniteDimensional (IsLocalRing.ResidueField A) (AdjoinRoot gbar) :=
    (AdjoinRoot.powerBasis (hg_irr.ne_zero)).finite
  haveI : FiniteDimensional (IsLocalRing.ResidueField A) (B ⧸ J) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hfr_eq : Module.finrank (IsLocalRing.ResidueField A) (AdjoinRoot gbar) =
    Module.finrank (IsLocalRing.ResidueField A) (B ⧸ J) := by
    have h1 : Module.finrank (IsLocalRing.ResidueField A) (AdjoinRoot gbar) = gbar.natDegree :=
      (AdjoinRoot.powerBasis (hg_irr.ne_zero)).finrank.trans
        (AdjoinRoot.powerBasis_dim (hg_irr.ne_zero))
    have h2 := hg_monic.natDegree_map (IsLocalRing.residue A)
    have h4 := (AdjoinRoot.isAdjoinRootMonic g hg_monic).finrank
    have h3 := @IsLocalRing.finrank_quotient_map A B _ _ _ _ _ _
    have : Module.finrank (IsLocalRing.ResidueField A) (B ⧸ J) =
      Module.finrank A B := by
      have : instAlg = Ideal.Quotient.algebraQuotientMapQuotient := by
        apply Algebra.algebra_ext
        intro c
        induction c using Quotient.inductionOn' with
        | h a =>
          show algMap_k (Ideal.Quotient.mk m a) = _
          exact Ideal.Quotient.lift_mk _ _ _
      rw [this]; exact h3
    linarith
  have hf_surj : Function.Surjective f := by
    have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr_eq
      (f := f.toLinearMap)).mp hf_inj
    exact this
  intro b
  obtain ⟨x, hx⟩ := hf_surj b
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (IsLocalRing.residue A)
    Ideal.Quotient.mk_surjective p
  refine ⟨AdjoinRoot.mk g P, ?_⟩
  rw [RingHom.comp_apply, ← hx, ← hP]
  show q ((AdjoinRoot.liftHom g α hα_aeval) (AdjoinRoot.mk g P)) =
    (AdjoinRoot.liftHom gbar (q α) haeval) (AdjoinRoot.mk gbar (Polynomial.map (IsLocalRing.residue A) P))
  erw [AdjoinRoot.liftHom_mk (f := g) (g := P), AdjoinRoot.liftHom_mk (f := gbar)]
  simp only [Polynomial.aeval_def]
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap (IsLocalRing.ResidueField A) (B ⧸ J)).comp
    (IsLocalRing.residue A) = q.comp (algebraMap A B) := by
    ext a; simp only [RingHom.comp_apply]; exact Ideal.Quotient.lift_mk _ _ _
  rw [hcomp, ← Polynomial.hom_eval₂ P (algebraMap A B) q α]

/--
[range_sup_maximalIdeal_smul_eq_top_of_adjoinRoot_liftHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma range_sup_maximalIdeal_smul_eq_top_of_adjoinRoot_liftHom
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B]
  [IsDomain B]
  [Algebra A B]
  [Module.Finite A B]
  {g : Polynomial A}
  {α : B}
-- given
  (hα_aeval : Polynomial.aeval α g = 0)
  (hg_monic : g.Monic)
  (hg_irr : Irreducible (g.map (IsLocalRing.residue A)))
  (hfinrank : Module.finrank A (AdjoinRoot g) = Module.finrank A B) :
-- imply
  LinearMap.range (AdjoinRoot.liftHom g α hα_aeval).toLinearMap ⊔ IsLocalRing.maximalIdeal A • ⊤ = ⊤ := by
-- proof
  set φ := AdjoinRoot.liftHom g α hα_aeval
  set m := IsLocalRing.maximalIdeal A
  rw [show (m • ⊤ : Submodule A B) = Submodule.restrictScalars A
    (Ideal.map (algebraMap A B) m) from Ideal.smul_top_eq_map m]
  rw [eq_top_iff]
  intro b _
  rw [Submodule.mem_sup]
  set J := Ideal.map (algebraMap A B) m
  set q : B →+* B ⧸ J := Ideal.Quotient.mk J
  have hsurj : Function.Surjective (q.comp φ.toRingHom) :=
    surjective_adjoinRoot_to_quotient g α hα_aeval hg_monic hg_irr hfinrank
  obtain ⟨c, hc⟩ := hsurj (q b)
  refine ⟨φ c, LinearMap.mem_range.mpr ⟨c, rfl⟩, b - φ c, ?_, by ring⟩
  rw [Submodule.restrictScalars_mem]
  have hc' : q (φ c) = q b := hc
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hc'
  exact J.neg_mem_iff.mp (show -(b - φ c) ∈ J by rwa [neg_sub])

/--
[dvr_unramified_monogenicity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma dvr_unramified_monogenicity
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [IsAdicComplete (maximalIdeal B) B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [IsUnramifiedDVRExtension A B] :
-- imply
  ∃ (g : Polynomial A) (_ : g.Monic), (g.map (residue A)).Separable ∧ Nonempty (B ≃ₐ[A] AdjoinRoot g) := by
-- proof
  set k := ResidueField A
  set l := ResidueField B
  haveI hsep := IsUnramifiedDVRExtension.residue_separable (A := A) (B := B)
  have hdeg := IsUnramifiedDVRExtension.degree_eq (A := A) (B := B)
  haveI hfinl : FiniteDimensional k l := finiteDimensional_residueField_of_finite_dvr A B
  haveI hBH : HenselianLocalRing B := henselian_dvr_extension_of_henselian (A := A) B
  obtain ⟨αbar, hαbar_top⟩ := Field.exists_primitive_element k l
  have hαbar_int : IsIntegral k αbar := Algebra.IsIntegral.isIntegral αbar
  set gbar := minpoly k αbar with hgbar_def
  have hgbar_monic : gbar.Monic := minpoly.monic hαbar_int
  have hgbar_irred : Irreducible gbar := minpoly.irreducible hαbar_int
  have hgbar_sep : gbar.Separable := Algebra.IsSeparable.isSeparable k αbar
  have hgbar_root : aeval αbar gbar = 0 := minpoly.aeval k αbar
  have hgbar_lifts : gbar ∈ Polynomial.lifts (residue A) := by
    rw [Polynomial.mem_lifts]
    exact (Polynomial.map_surjective _ residue_surjective gbar).imp fun _ hq => hq
  obtain ⟨g, hg_map, hg_natdeg, hg_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hgbar_lifts hgbar_monic
  have hg_sep : (g.map (residue A)).Separable := hg_map ▸ hgbar_sep
  have hg_irr : Irreducible (g.map (residue A)) := hg_map ▸ hgbar_irred
  set gB := g.map (algebraMap A B)
  have hgB_monic : gB.Monic := hg_monic.map (algebraMap A B)
  obtain ⟨α₀, hα₀⟩ := residue_surjective (R := B) αbar
  have heval_mem : Polynomial.eval α₀ gB ∈ maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro h_unit
    have hne : residue B (Polynomial.eval α₀ gB) ≠ 0 :=
      ((residue B).isUnit_map h_unit).ne_zero
    apply hne
    show residue B (Polynomial.eval α₀ (Polynomial.map (algebraMap A B) g)) = 0
    rw [← Polynomial.eval_map_apply (residue B) α₀, Polynomial.map_map]
    have hcompat : (residue B).comp (algebraMap A B) =
      (algebraMap k l).comp (residue A) := by
      rw [show algebraMap k l = IsLocalRing.ResidueField.map (algebraMap A B) from rfl]
      exact (IsLocalRing.ResidueField.map_comp_residue (algebraMap A B)).symm
    rw [hcompat, ← Polynomial.map_map, hg_map, Polynomial.eval_map, ← Polynomial.aeval_def,
      hα₀, hgbar_root]
  have hderiv_unit : IsUnit (Polynomial.eval α₀ gB.derivative) := by
    rw [IsLocalRing.notMem_maximalIdeal.symm]
    intro hmem
    have h0 : residue B (Polynomial.eval α₀ (Polynomial.derivative (Polynomial.map (algebraMap A B) g))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [Polynomial.derivative_map] at h0
    rw [← Polynomial.eval_map_apply (residue B) α₀, Polynomial.map_map] at h0
    have hcompat : (residue B).comp (algebraMap A B) =
      (algebraMap k l).comp (residue A) := by
      rw [show algebraMap k l = IsLocalRing.ResidueField.map (algebraMap A B) from rfl]
      exact (IsLocalRing.ResidueField.map_comp_residue (algebraMap A B)).symm
    rw [hcompat, ← Polynomial.map_map, ← Polynomial.derivative_map, hg_map,
      Polynomial.eval_map, ← Polynomial.aeval_def, hα₀] at h0
    exact hgbar_sep.aeval_derivative_ne_zero hgbar_root h0
  obtain ⟨α, hα_root, _⟩ := HenselianLocalRing.is_henselian gB hgB_monic α₀ heval_mem hderiv_unit
  have hα_aeval : aeval α g = 0 := by
    rwa [aeval_def, ← Polynomial.eval_map]
  let φ := AdjoinRoot.liftHom g α hα_aeval
  haveI := adjoinRoot_module_finite_of_monic g hg_monic
  haveI := adjoinRoot_isDomain_of_irreducible_mod g hg_monic hg_irr
  have hfinrank : Module.finrank A (AdjoinRoot g) = Module.finrank A B := by
    rw [finrank_adjoinRoot_of_monic g hg_monic, hg_natdeg]
    have hnd : gbar.natDegree = Module.finrank k l := by
      rw [← IntermediateField.adjoin.finrank hαbar_int, hαbar_top,
        IntermediateField.finrank_top']
    rw [hnd]; exact hdeg.symm
  have hsup : LinearMap.range φ.toLinearMap ⊔
    IsLocalRing.maximalIdeal A • ⊤ = ⊤ := by
    exact range_sup_maximalIdeal_smul_eq_top_of_adjoinRoot_liftHom
      g α hα_aeval hg_monic hg_irr hfinrank
  have hsurj : Function.Surjective φ :=
    surjective_of_range_sup_maximalIdeal_smul_eq_top φ hsup
  have hinj : Function.Injective φ :=
    injective_of_surjective_of_finrank_eq_of_domain φ hfinrank hsurj
  exact ⟨g, hg_monic, hg_sep, ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩⟩

/--
[adjoinRoot_minpoly_ringEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoinRoot_minpoly_ringEquiv
  [Field k]
  [Field l]
  [Algebra k l]
  [FiniteDimensional k l]
  {α : l}
-- given
  (hα : IntermediateField.adjoin k ({α} : Set l) = ⊤)
  (hint : IsIntegral k α) :
-- imply
  Nonempty (AdjoinRoot (minpoly k α) ≃+* l) := by
-- proof
  haveI : Fact (Irreducible (minpoly k α)) := ⟨minpoly.irreducible hint⟩
  let φ := AdjoinRoot.liftHom (minpoly k α) α (minpoly.aeval k α)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have _hfinA : FiniteDimensional k (AdjoinRoot (minpoly k α)) :=
    (AdjoinRoot.powerBasis' (minpoly.monic hint)).finite
  have hdim : Module.finrank k (AdjoinRoot (minpoly k α)) = Module.finrank k l := by
    rw [(AdjoinRoot.powerBasis' (minpoly.monic hint)).finrank]
    simp only [AdjoinRoot.powerBasis']
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := φ.toLinearMap)).mp hinj
  exact ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).toRingEquiv⟩
section ResidueHelpers
variable {A : Type*} [CommRing A] [IsLocalRing A]
  {B : Type*} [CommRing B] [IsLocalRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)]

/--
[residue_comp_algebraMap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma residue_comp_algebraMap_eq
  [CommRing A]
  [IsLocalRing A] :
-- imply
  (residue B).comp (algebraMap A B) = (algebraMap (ResidueField A) (ResidueField B)).comp (residue A) := by
-- proof
  ext a; rfl

/--
[residue_aeval_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma residue_aeval_eq
  [CommRing A]
  [IsLocalRing A]
  {p : A[X]}
  {b : B} :
-- imply
  residue B (aeval b p) = aeval (residue B b) (p.map (residue A)) := by
-- proof
  simp only [aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂,
    residue_comp_algebraMap_eq]

/--
[adjoin_residue_top_of_adjoin_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma adjoin_residue_top_of_adjoin_top
  [CommRing A]
  [IsLocalRing A]
  {α : B}
-- given
  (htop : Algebra.adjoin A ({α} : Set B) = ⊤) :
-- imply
  Algebra.adjoin (ResidueField A) ({residue B α} : Set (ResidueField B)) = ⊤ := by
-- proof
  rw [eq_top_iff]
  intro x _
  obtain ⟨b, rfl⟩ := residue_surjective x
  have hb : b ∈ Algebra.adjoin A ({α} : Set B) := htop ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb ⊢
  obtain ⟨p, rfl⟩ := hb
  show residue B ((aeval α) p) ∈ (aeval (residue B α)).range
  rw [residue_aeval_eq]
  exact ⟨p.map (residue A), rfl⟩
end ResidueHelpers
section ResidueFieldFunctorFullFaithfulness
variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {B₁ : Type*} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
variable {B₂ : Type*} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]

/--
[dvr_extension_henselian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma dvr_extension_henselian
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B₁]
  [IsDomain B₁]
  [IsDiscreteValuationRing B₁]
  [CommRing B₂]
  [IsDomain B₂]
  [IsDiscreteValuationRing B₂]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [IsAdicComplete (IsLocalRing.maximalIdeal B) B] :
-- imply
  HenselianLocalRing B := by
-- proof
  have hH := IsAdicComplete.henselianRing B (IsLocalRing.maximalIdeal B)
  exact {
    is_henselian := fun f hfm a₀ hfa₀ hunit => by
      have hunit' : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)
        (Polynomial.eval a₀ (Polynomial.derivative f))) :=
        hunit.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B))
      exact hH.is_henselian f hfm a₀ hfa₀ hunit'
  }

/--
[residueFieldFunctor_full_faithfulness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma residueFieldFunctor_full_faithfulness
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B₁]
  [IsDomain B₁]
  [IsDiscreteValuationRing B₁]
  [CommRing B₂]
  [IsDomain B₂]
  [IsDiscreteValuationRing B₂]
  [IsUnramifiedDVRExtension A B₁]
  [IsUnramifiedDVRExtension A B₂] :
-- imply
  Function.Bijective (residueFieldFunctorAlg (A := A) (B₁ := B₁) (B₂ := B₂)) := by
-- proof
  obtain ⟨g, hg_monic, hg_sep, ⟨iso⟩⟩ := dvr_unramified_monogenicity A B₁
  haveI : HenselianLocalRing B₂ := dvr_extension_henselian B₂
  set g' := g.map (algebraMap A B₂) with hg'_def
  have hg'_monic : g'.Monic := hg_monic.map (algebraMap A B₂)
  have hg'_sep : (g'.map (residue B₂)).Separable := by
    simp only [hg'_def, Polynomial.map_map]
    have key : (residue B₂).comp (algebraMap A B₂) =
      (ResidueField.map (algebraMap A B₂)).comp (residue A) := by
      ext a; exact (ResidueField.map_residue (algebraMap A B₂) a).symm
    rw [key, ← Polynomial.map_map]
    exact Separable.map hg_sep
  set α := iso.symm (AdjoinRoot.root g) with hα_def
  have hα_top : Algebra.adjoin A ({α} : Set B₁) = ⊤ := by
    rw [eq_top_iff]; intro b _
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    have hb_mem : iso b ∈ (⊤ : Subalgebra A (AdjoinRoot g)) := Algebra.mem_top
    rw [← AdjoinRoot.adjoinRoot_eq_top] at hb_mem
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb_mem
    obtain ⟨p, hp⟩ := hb_mem
    exact ⟨p, by
      change aeval (iso.symm (AdjoinRoot.root g)) p = b
      have h1 : aeval (iso.symm (AdjoinRoot.root g)) p =
        iso.symm (aeval (AdjoinRoot.root g) p) := by simp [aeval_algHom_apply]
      rw [h1]
      have h2 : (aeval (AdjoinRoot.root g) p : AdjoinRoot g) = iso b := by
        change (aeval (AdjoinRoot.root g)).toRingHom p = iso b; exact hp
      rw [h2, AlgEquiv.symm_apply_apply]⟩
  set β_bar := residue B₁ α with hβ_bar_def
  have hβ_gen : Algebra.adjoin (ResidueField A) ({β_bar} : Set (ResidueField B₁)) = ⊤ :=
    adjoin_residue_top_of_adjoin_top α hα_top
  have h_α_root : aeval α g = 0 := by
    rw [show aeval α g = iso.symm (aeval (AdjoinRoot.root g) g) from
      by simp [hα_def, aeval_algHom_apply]]
    simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h_β_root_red : (Polynomial.map (algebraMap (ResidueField A) (ResidueField B₁))
    (g.map (residue A))).IsRoot β_bar := by
    have h1 : (g.map (algebraMap A B₁)).IsRoot α := by
      simp only [Polynomial.IsRoot, Polynomial.eval_map, ← aeval_def]; exact h_α_root
    have h2 := root_maps_to_residue_root h1
    rwa [Polynomial.map_map, residue_comp_algebraMap_eq, ← Polynomial.map_map] at h2
  constructor
  ·
    intro φ₁ φ₂ heq
    set ψ₁ := φ₁.comp iso.symm.toAlgHom with hψ₁_def
    set ψ₂ := φ₂.comp iso.symm.toAlgHom with hψ₂_def
    have hr₁ : aeval (ψ₁ (AdjoinRoot.root g)) g = 0 := by
      rw [show aeval (ψ₁ (AdjoinRoot.root g)) g =
        ψ₁ (aeval (AdjoinRoot.root g) g) from by simp [aeval_algHom_apply]]
      simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hr₂ : aeval (ψ₂ (AdjoinRoot.root g)) g = 0 := by
      rw [show aeval (ψ₂ (AdjoinRoot.root g)) g =
        ψ₂ (aeval (AdjoinRoot.root g) g) from by simp [aeval_algHom_apply]]
      simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hr₁' : g'.IsRoot (ψ₁ (AdjoinRoot.root g)) := by
      simp only [Polynomial.IsRoot, hg'_def, Polynomial.eval_map, ← aeval_def]; exact hr₁
    have hr₂' : g'.IsRoot (ψ₂ (AdjoinRoot.root g)) := by
      simp only [Polynomial.IsRoot, hg'_def, Polynomial.eval_map, ← aeval_def]; exact hr₂
    have hres_eq : residue B₂ (ψ₁ (AdjoinRoot.root g)) =
      residue B₂ (ψ₂ (AdjoinRoot.root g)) := by
      have h_eq_fn : ∀ x : ResidueField B₁,
        (residueFieldFunctorAlg φ₁ : ResidueField B₁ →+* ResidueField B₂) x =
        (residueFieldFunctorAlg φ₂ : ResidueField B₁ →+* ResidueField B₂) x := by
        intro x; exact congr_fun (congr_arg DFunLike.coe (congr_arg AlgHom.toRingHom heq)) x
      have h_loc₁ := algHom_dvr_isLocalHom φ₁
      have h_loc₂ := algHom_dvr_isLocalHom φ₂
      show (residue B₂) (φ₁ (iso.symm (AdjoinRoot.root g))) =
        (residue B₂) (φ₂ (iso.symm (AdjoinRoot.root g)))
      rw [show (residue B₂) (φ₁ (iso.symm (AdjoinRoot.root g))) =
        (@ResidueField.map B₁ B₂ _ _ _ _ φ₁.toRingHom h_loc₁)
          ((residue B₁) (iso.symm (AdjoinRoot.root g))) from
        (ResidueField.map_residue φ₁.toRingHom _).symm]
      rw [show (residue B₂) (φ₂ (iso.symm (AdjoinRoot.root g))) =
        (@ResidueField.map B₁ B₂ _ _ _ _ φ₂.toRingHom h_loc₂)
          ((residue B₁) (iso.symm (AdjoinRoot.root g))) from
        (ResidueField.map_residue φ₂.toRingHom _).symm]
      exact h_eq_fn _
    have hroots_eq : ψ₁ (AdjoinRoot.root g) = ψ₂ (AdjoinRoot.root g) :=
      hensel_root_injective hg'_monic hg'_sep hr₁' hr₂' hres_eq
    have hψ_eq : ψ₁ = ψ₂ := AdjoinRoot.algHom_ext hroots_eq
    have h_comp := congr_arg (· |>.comp iso.toAlgHom) hψ_eq
    have key : (iso.symm.toAlgHom).comp iso.toAlgHom = AlgHom.id A B₁ := by ext x; simp
    simp only [hψ₁_def, hψ₂_def, AlgHom.comp_assoc, key, AlgHom.comp_id] at h_comp
    exact h_comp
  ·
    intro f
    haveI : IsLocalHom (AdjoinRoot.of g) := by
      have : AdjoinRoot.of g = iso.toAlgHom.toRingHom.comp (algebraMap A B₁) := by
        ext a; exact (iso.commutes a).symm
      rw [this]
      haveI : IsLocalHom iso.toAlgHom.toRingHom := by
        constructor; intro a ha
        rw [isUnit_iff_exists_inv] at ha ⊢
        obtain ⟨b, hb⟩ := ha
        exact ⟨iso.symm b, by have := congr_arg iso.symm hb; simp at this; exact this⟩
      exact RingHom.isLocalHom_comp _ _
    have h_f_β_root : (g'.map (residue B₂)).IsRoot (f β_bar) := by
      have h_f_root : (Polynomial.map (algebraMap (ResidueField A) (ResidueField B₂))
        (g.map (residue A))).IsRoot (f β_bar) := by
        simp only [Polynomial.IsRoot, Polynomial.eval_map, ← aeval_def] at h_β_root_red ⊢
        rw [show aeval (f β_bar) (Polynomial.map (residue A) g) =
          f (aeval β_bar (Polynomial.map (residue A) g)) from by simp [aeval_algHom_apply]]
        simp [h_β_root_red]
      simp only [hg'_def, Polynomial.map_map] at h_f_root ⊢
      have key : (residue B₂).comp (algebraMap A B₂) =
        (algebraMap (ResidueField A) (ResidueField B₂)).comp (residue A) := by
        ext a; exact (ResidueField.map_residue (algebraMap A B₂) a).symm
      rwa [key]
    obtain ⟨b₀, hb₀_root, hb₀_res⟩ :=
      hensel_root_lift hg'_monic hg'_sep h_f_β_root
    have hb₀_aeval : aeval b₀ g = 0 := by
      have := hb₀_root
      simp only [Polynomial.IsRoot, hg'_def, Polynomial.eval_map, ← aeval_def] at this
      exact this
    let ψ : AdjoinRoot g →ₐ[A] B₂ := AdjoinRoot.liftHom g b₀ hb₀_aeval
    let φ : B₁ →ₐ[A] B₂ := ψ.comp iso.toAlgHom
    refine ⟨φ, ?_⟩
    apply AlgHom.ext_of_adjoin_eq_top hβ_gen
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    show (residueFieldFunctorAlg φ) β_bar = f β_bar
    change @ResidueField.map B₁ B₂ _ _ _ _ φ.toRingHom (algHom_dvr_isLocalHom φ)
      (residue B₁ α) = f β_bar
    rw [ResidueField.map_residue]
    show residue B₂ (ψ (iso α)) = f β_bar
    rw [show iso α = AdjoinRoot.root g from by simp [hα_def]]
    show residue B₂ (ψ (AdjoinRoot.root g)) = f β_bar
    have : ψ (AdjoinRoot.root g) = b₀ :=
      AdjoinRoot.liftHom_root (f := g) (a := b₀) (hfx := hb₀_aeval)
    rw [this, hb₀_res]
end ResidueFieldFunctorFullFaithfulness
section ResidueFieldFunctorEssentialSurjectivity
variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]

/--
[residueFieldFunctor_essential_surjectivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma residueFieldFunctor_essential_surjectivity
  {A : Type}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {l : Type}
  [Field l]
  [Algebra (ResidueField A) l]
  [FiniteDimensional (ResidueField A) l]
  [Algebra.IsSeparable (ResidueField A) l] :
-- imply
  ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)) (_ : Module.Finite A B), ∃ (hAlg : Algebra (ResidueField A) (ResidueField B)) (_ : @FiniteDimensional (ResidueField A) (ResidueField B) _ _ hAlg.toModule) (_ : @Algebra.IsSeparable (ResidueField A) (ResidueField B) _ _ hAlg), Nonempty (ResidueField B ≃+* l) := by
-- proof
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) l
  have hint : IsIntegral (ResidueField A) α := Algebra.IsIntegral.isIntegral α
  have hgbar_monic := minpoly.monic hint
  have hgbar_irred := minpoly.irreducible hint
  have hgbar_sep : (minpoly (ResidueField A) α).Separable :=
    (Algebra.IsSeparable.isSeparable' α : IsSeparable (ResidueField A) α)
  obtain ⟨g, _, _, hID, hDVR, hLH, hMF, hAlg, hFD, hSep, ⟨e1⟩⟩ :=
    adjoinRoot_dvr_of_irreducible_lift A (minpoly (ResidueField A) α)
      hgbar_monic hgbar_irred hgbar_sep
  obtain ⟨e2⟩ := adjoinRoot_minpoly_ringEquiv α hα hint
  exact ⟨AdjoinRoot g, inferInstance, hID, hDVR, inferInstance, hLH, hMF,
    hAlg, hFD, hSep, ⟨e1.trans e2⟩⟩
end ResidueFieldFunctorEssentialSurjectivity
section ResidueFieldFunctorInjectivity
variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {B₁ : Type*} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
variable {B₂ : Type*} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]

/--
[residueFieldFunctor_injectivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma residueFieldFunctor_injectivity
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B₁]
  [IsDomain B₁]
  [IsDiscreteValuationRing B₁]
  [CommRing B₂]
  [IsDomain B₂]
  [IsDiscreteValuationRing B₂]
  [IsUnramifiedDVRExtension A B₁]
  [IsUnramifiedDVRExtension A B₂]
  {e : ResidueField B₁ ≃ₐ[ResidueField A] ResidueField B₂} :
-- imply
  Nonempty (B₁ ≃ₐ[A] B₂) := by
-- proof
  have hff₁₂ := residueFieldFunctor_full_faithfulness (A := A) (B₁ := B₁) (B₂ := B₂)
  obtain ⟨φ, hφ⟩ := hff₁₂.2 e.toAlgHom
  have hff₂₁ := residueFieldFunctor_full_faithfulness (A := A) (B₁ := B₂) (B₂ := B₁)
  obtain ⟨ψ, hψ⟩ := hff₂₁.2 e.symm.toAlgHom
  haveI : IsLocalHom φ.toRingHom := algHom_dvr_isLocalHom φ
  haveI : IsLocalHom ψ.toRingHom := algHom_dvr_isLocalHom ψ
  have hφ_all : ∀ x : ResidueField B₁, ResidueField.map φ.toRingHom x = e x := by
    intro x; exact AlgHom.congr_fun hφ x
  have hψ_all : ∀ x : ResidueField B₂, ResidueField.map ψ.toRingHom x = e.symm x := by
    intro x; exact AlgHom.congr_fun hψ x
  have hff₁₁ := residueFieldFunctor_full_faithfulness (A := A) (B₁ := B₁) (B₂ := B₁)
  have hcomp₁ : ψ.comp φ = AlgHom.id A B₁ := by
    apply hff₁₁.1
    apply AlgHom.ext
    intro x
    obtain ⟨b₁, rfl⟩ := residue_surjective x
    change @ResidueField.map B₁ B₁ _ _ _ _ (ψ.comp φ).toRingHom
      (algHom_dvr_isLocalHom (ψ.comp φ)) (residue B₁ b₁) =
      @ResidueField.map B₁ B₁ _ _ _ _ (AlgHom.id A B₁).toRingHom
        (algHom_dvr_isLocalHom (AlgHom.id A B₁)) (residue B₁ b₁)
    haveI : IsLocalHom (ψ.comp φ).toRingHom := algHom_dvr_isLocalHom (ψ.comp φ)
    haveI : IsLocalHom (AlgHom.id A B₁).toRingHom := algHom_dvr_isLocalHom (AlgHom.id A B₁)
    rw [ResidueField.map_residue, ResidueField.map_residue]
    show residue B₁ (ψ (φ b₁)) = residue B₁ b₁
    rw [show residue B₁ (ψ (φ b₁)) =
      ResidueField.map ψ.toRingHom (residue B₂ (φ b₁)) from
      (ResidueField.map_residue ψ.toRingHom (φ b₁)).symm,
      show residue B₂ (φ b₁) =
        ResidueField.map φ.toRingHom (residue B₁ b₁) from
      (ResidueField.map_residue φ.toRingHom b₁).symm]
    rw [hφ_all, hψ_all]
    simp [AlgEquiv.symm_apply_apply]
  have hff₂₂ := residueFieldFunctor_full_faithfulness (A := A) (B₁ := B₂) (B₂ := B₂)
  have hcomp₂ : φ.comp ψ = AlgHom.id A B₂ := by
    apply hff₂₂.1
    apply AlgHom.ext
    intro x
    obtain ⟨b₂, rfl⟩ := residue_surjective x
    change @ResidueField.map B₂ B₂ _ _ _ _ (φ.comp ψ).toRingHom
      (algHom_dvr_isLocalHom (φ.comp ψ)) (residue B₂ b₂) =
      @ResidueField.map B₂ B₂ _ _ _ _ (AlgHom.id A B₂).toRingHom
        (algHom_dvr_isLocalHom (AlgHom.id A B₂)) (residue B₂ b₂)
    haveI : IsLocalHom (φ.comp ψ).toRingHom := algHom_dvr_isLocalHom (φ.comp ψ)
    haveI : IsLocalHom (AlgHom.id A B₂).toRingHom := algHom_dvr_isLocalHom (AlgHom.id A B₂)
    rw [ResidueField.map_residue, ResidueField.map_residue]
    show residue B₂ (φ (ψ b₂)) = residue B₂ b₂
    rw [show residue B₂ (φ (ψ b₂)) =
      ResidueField.map φ.toRingHom (residue B₁ (ψ b₂)) from
      (ResidueField.map_residue φ.toRingHom (ψ b₂)).symm,
      show residue B₁ (ψ b₂) =
        ResidueField.map ψ.toRingHom (residue B₂ b₂) from
      (ResidueField.map_residue ψ.toRingHom b₂).symm]
    rw [hψ_all, hφ_all]
    simp [AlgEquiv.apply_symm_apply]
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 := AlgHom.congr_fun hcomp₁ a
    have h2 := AlgHom.congr_fun hcomp₁ b
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at h1 h2
    rw [← h1, ← h2]
    exact congr_arg ψ hab
  have hsurj : Function.Surjective φ := by
    intro b
    refine ⟨ψ b, ?_⟩
    have := AlgHom.congr_fun hcomp₂ b
    simp only [AlgHom.comp_apply, AlgHom.id_apply] at this
    exact this
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩
end ResidueFieldFunctorInjectivity
section ResidueFieldFunctorEquivalence
variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [HenselianLocalRing A]
variable {B₁ : Type} [CommRing B₁] [IsDomain B₁] [IsDiscreteValuationRing B₁]
  [Algebra A B₁] [IsLocalHom (algebraMap A B₁)] [Module.Finite A B₁]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₁) B₁]
variable {B₂ : Type} [CommRing B₂] [IsDomain B₂] [IsDiscreteValuationRing B₂]
  [Algebra A B₂] [IsLocalHom (algebraMap A B₂)] [Module.Finite A B₂]
  [IsAdicComplete (IsLocalRing.maximalIdeal B₂) B₂]

/--
[residueFieldFunctor_isEquivalence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
lemma residueFieldFunctor_isEquivalence
  {A : Type}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B₁ : Type}
  [CommRing B₁]
  [IsDomain B₁]
  [IsDiscreteValuationRing B₁]
  {B₂ : Type}
  [CommRing B₂]
  [IsDomain B₂]
  [IsDiscreteValuationRing B₂]
  [IsUnramifiedDVRExtension A B₁]
  [IsUnramifiedDVRExtension A B₂] :
-- imply
  (Function.Bijective (residueFieldFunctorAlg (A := A) (B₁ := B₁) (B₂ := B₂))) ∧ (∀ (l : Type) [Field l] [Algebra (ResidueField A) l] [FiniteDimensional (ResidueField A) l] [Algebra.IsSeparable (ResidueField A) l], ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)) (_ : Module.Finite A B), ∃ (hAlg : Algebra (ResidueField A) (ResidueField B)) (_ : @FiniteDimensional (ResidueField A) (ResidueField B) _ _ hAlg.toModule) (_ : @Algebra.IsSeparable (ResidueField A) (ResidueField B) _ _ hAlg), Nonempty (ResidueField B ≃+* l)) ∧ (∀ (_ : ResidueField B₁ ≃ₐ[ResidueField A] ResidueField B₂), Nonempty (B₁ ≃ₐ[A] B₂)) :=
-- proof
  ⟨residueFieldFunctor_full_faithfulness,
    fun l => residueFieldFunctor_essential_surjectivity l,
    residueFieldFunctor_injectivity⟩
end ResidueFieldFunctorEquivalence

/--
[dvr_ker_algebraMap_absurd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
private lemma dvr_ker_algebraMap_absurd_eq
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [Module.Finite A B]
-- given
  (h_le : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A B)) :
-- imply
  False := by
-- proof
  apply dvr_ker_algebraMap_absurd A B h_le

/--
[algHom_dvr_isLocalHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ResidueFieldFunctor.lean)
-/
@[path]
private lemma algHom_dvr_isLocalHom_eq
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [CommRing B₁]
  [IsDomain B₁]
  [IsDiscreteValuationRing B₁]
  [CommRing B₂]
  [IsDomain B₂]
  [IsDiscreteValuationRing B₂]
  {φ : B₁ →ₐ[A] B₂} :
-- imply
  IsLocalHom φ.toRingHom := by
-- proof
  apply algHom_dvr_isLocalHom φ


-- created on 2026-10-23
