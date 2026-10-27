import Mathlib
import Lemma.HeckeEis.BinaryFormRep
import Lemma.Gamma0CoeffCohomology.Main
import Initialize.Tactic.Attr.Basic
open HeckeEis
open MvPolynomial
set_option autoImplicit false


namespace Definitions
end Definitions

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

private lemma coeffCocycles_apply_one {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have : z 1 + z 1 = z 1 + 0 := (add_zero (z 1)).symm ▸ h.symm
  exact add_left_cancel this

private lemma coeffCocycles_apply_inv {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) (g : G) : z g⁻¹ = -(ρ g⁻¹ (z g)) := by
  have h := hz g⁻¹ g
  rw [inv_mul_cancel, coeffCocycles_apply_one hz] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private lemma mem_of_mem_coeffCocycles_of_closure_eq_top {ρ : Representation K G V} {z : G → V} (hz : z ∈ coeffCocycles ρ) (M : AddSubgroup V) (hM : ∀ (g : G) (v : V), v ∈ M → ρ g v ∈ M) {s : Set G} (hs : Subgroup.closure s = ⊤) (h : ∀ g ∈ s, z g ∈ M) (g : G) : z g ∈ M := by
  let H : Subgroup G :=
    { carrier := {g | z g ∈ M}
      one_mem' := by
        show z 1 ∈ M
        simp [coeffCocycles_apply_one hz]
      mul_mem' := by
        intro a b ha hb
        show z (a * b) ∈ M
        rw [hz a b]
        exact M.add_mem ha (hM a _ hb)
      inv_mem' := by
        intro a ha
        show z a⁻¹ ∈ M
        rw [coeffCocycles_apply_inv hz]
        exact M.neg_mem (hM _ _ ha) }
  exact (by rwa [← hs, Subgroup.closure_le] : (⊤ : Subgroup G) ≤ H) (Subgroup.mem_top g)

private lemma coeffCocycles_eq_of_eqOn {ρ : Representation K G V} {z z' : G → V} (hz : z ∈ coeffCocycles ρ) (hz' : z' ∈ coeffCocycles ρ) {s : Set G} (hs : Subgroup.closure s = ⊤) (h : ∀ g ∈ s, z g = z' g) : z = z' := by
  have hd : z - z' ∈ coeffCocycles ρ := Submodule.sub_mem _ hz hz'
  funext g
  have := mem_of_mem_coeffCocycles_of_closure_eq_top hd ⊥ (fun g v hv => by
    rw [AddSubgroup.mem_bot] at hv ⊢; rw [hv, map_zero]) hs (fun g hg => by
    rw [AddSubgroup.mem_bot, Pi.sub_apply, h g hg, sub_self]) g
  rw [AddSubgroup.mem_bot, Pi.sub_apply] at this
  exact sub_eq_zero.mp this

variable {R R' : Type*} [CommRing R] [CommRing R']

private lemma binarySubst_eq_bind₁ (S : Type*) [CommRing S] (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) S) : binarySubst S M P = bind₁ (fun j => ∑ i : Fin 2, C ((M i j : ℤ) : S) * X i) P := by
  rw [binarySubst, aeval_eq_bind₁]

private lemma map_binarySubst_int (φ : ℤ →+* R) (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) ℤ) : MvPolynomial.map φ (binarySubst ℤ M P) = binarySubst R M (MvPolynomial.map φ P) :=
  RingHom.congr_fun (MvPolynomial.ringHom_ext (fun a => by simp) (fun j => by simp [binarySubst_X]) :
    (MvPolynomial.map φ).comp (binarySubst ℤ M : MvPolynomial (Fin 2) ℤ →ₐ[ℤ] MvPolynomial (Fin 2) ℤ).toRingHom =
      (binarySubst R M : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R).toRingHom.comp (MvPolynomial.map φ)) P

noncomputable def substCoeff (M : Matrix (Fin 2) (Fin 2) ℤ) (d d' : Finsupp (Fin 2) ℕ) : ℤ := (binarySubst ℤ M (monomial d' 1)).coeff d

private lemma binarySubst_monomial_one (M : Matrix (Fin 2) (Fin 2) ℤ) (d' : Finsupp (Fin 2) ℕ) : binarySubst R M (monomial d' 1) = MvPolynomial.map (Int.castRingHom R) (binarySubst ℤ M (monomial d' 1)) := by
  rw [map_binarySubst_int, map_monomial, (Int.castRingHom R).map_one]

private lemma coeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) (d : Finsupp (Fin 2) ℕ) : (binarySubst R M P).coeff d = ∑ d' ∈ P.support, (substCoeff M d d' : R) * P.coeff d' := by
  conv_lhs => rw [P.as_sum, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [show monomial d' (P.coeff d') = C (P.coeff d') * monomial d' 1 by rw [C_mul_monomial, mul_one], map_mul, binarySubst_C,
    coeff_C_mul, binarySubst_monomial_one, coeff_map, substCoeff, mul_comm]
  rfl

variable (f : AddMonoidHom R R')

noncomputable def pushCoeff (P : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R' := ∑ d ∈ P.support, monomial d (f (P.coeff d))

@[simp] private lemma coeff_pushCoeff (P : MvPolynomial (Fin 2) R) (d : Finsupp (Fin 2) ℕ) : (pushCoeff f P).coeff d = f (P.coeff d) := by
  classical
  rw [pushCoeff, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

private lemma support_pushCoeff (P : MvPolynomial (Fin 2) R) : (pushCoeff f P).support ⊆ P.support := by
  intro d hd
  rw [mem_support_iff, coeff_pushCoeff] at hd
  rw [mem_support_iff]
  intro h; exact hd (by rw [h, map_zero])

private lemma pushCoeff_mem (n : ℕ) {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : pushCoeff f P ∈ BinaryForm R' n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  intro d hd
  exact hP (mem_support_iff.mp (support_pushCoeff f P (mem_support_iff.mpr hd)))

private lemma pushCoeff_add (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P + Q) = pushCoeff f P + pushCoeff f Q := by
  ext d; simp

private lemma pushCoeff_sub (P Q : MvPolynomial (Fin 2) R) : pushCoeff f (P - Q) = pushCoeff f P - pushCoeff f Q := by
  ext d; simp

private lemma pushCoeff_zero : pushCoeff f (0 : MvPolynomial (Fin 2) R) = 0 := by
  ext d; simp

private lemma eq_pushCoeff_iff (P : MvPolynomial (Fin 2) R) (Q : MvPolynomial (Fin 2) R') : Q = pushCoeff f P ↔ ∀ d, Q.coeff d = f (P.coeff d) := by
  constructor
  ·
    rintro rfl d
    exact coeff_pushCoeff f P d
  ·
    intro h
    ext d
    rw [h d, coeff_pushCoeff]

private lemma pushCoeff_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (P : MvPolynomial (Fin 2) R) : pushCoeff f (binarySubst R M P) = binarySubst R' M (pushCoeff f P) := by
  classical
  ext d
  rw [coeff_pushCoeff, coeff_binarySubst, coeff_binarySubst, map_sum]
  rw [Finset.sum_subset (support_pushCoeff f P)]
  ·
    refine Finset.sum_congr rfl fun d' _ => ?_
    rw [coeff_pushCoeff, ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul]
  ·
    intro d' _ hd'
    rw [notMem_support_iff.mp hd', mul_zero]

noncomputable def pushForm (n : ℕ) (P : ↥(BinaryForm R n)) : ↥(BinaryForm R' n) := ⟨pushCoeff f P, pushCoeff_mem f n P.2⟩

@[simp] private lemma coe_pushForm (n : ℕ) (P : ↥(BinaryForm R n)) : ((pushForm f n P : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = pushCoeff f P := rfl

private lemma pushForm_add (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P + Q) = pushForm f n P + pushForm f n Q := Subtype.ext (by simp [pushCoeff_add])

private lemma pushForm_sub (n : ℕ) (P Q : ↥(BinaryForm R n)) : pushForm f n (P - Q) = pushForm f n P - pushForm f n Q := Subtype.ext (by simp [pushCoeff_sub])

private lemma pushForm_zero (n : ℕ) : pushForm f n (0 : ↥(BinaryForm R n)) = 0 := Subtype.ext (by simp [pushCoeff_zero])

private lemma pushForm_binaryFormRepSL (n : ℕ) (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (P : ↥(BinaryForm R n)) : pushForm f n (binaryFormRepSL R n g P) = binaryFormRepSL R' n g (pushForm f n P) := Subtype.ext (by simp [pushCoeff_binarySubst])

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (n : ℕ)

private lemma pushForm_comp_mem_coeffCocycles {z : Γ → ↥(BinaryForm R n)} (hz : z ∈ coeffCocycles ((binaryFormRepSL R n).comp Γ.subtype)) : (fun g => pushForm f n (z g)) ∈ coeffCocycles ((binaryFormRepSL R' n).comp Γ.subtype) := by
  intro g h
  show pushForm f n (z (g * h)) = pushForm f n (z g) + binaryFormRepSL R' n ((g : Γ) : Matrix.SpecialLinearGroup (Fin 2) ℤ) (pushForm f n (z h))
  rw [hz g h, pushForm_add, ← pushForm_binaryFormRepSL]
  rfl

private lemma isParabolicCocycle_pushForm_comp {z : Γ → ↥(BinaryForm R n)} (hz : IsParabolicCocycle ((binaryFormRepSL R n).comp Γ.subtype) z) : IsParabolicCocycle ((binaryFormRepSL R' n).comp Γ.subtype) (fun g => pushForm f n (z g)) := by
  intro γ hγ
  obtain ⟨u, hu⟩ := hz γ hγ
  refine ⟨pushForm f n u, ?_⟩
  rw [LinearMap.sub_apply, Module.End.one_apply] at hu ⊢
  change binaryFormRepSL R n (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) u - u = z γ at hu
  show binaryFormRepSL R' n (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (pushForm f n u) - pushForm f n u = pushForm f n (z γ)
  rw [← hu, pushForm_sub, pushForm_binaryFormRepSL]

private lemma pushForm_comp_mem_coeffParabolicCocycles {z : Γ → ↥(BinaryForm R n)} (hz : z ∈ coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype)) : (fun g => pushForm f n (z g)) ∈ coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype) := ⟨pushForm_comp_mem_coeffCocycles f n hz.1, isParabolicCocycle_pushForm_comp f n hz.2⟩

private lemma pushForm_comp_mem_coeffCoboundaries {z : Γ → ↥(BinaryForm R n)} (hz : z ∈ coeffCoboundaries ((binaryFormRepSL R n).comp Γ.subtype)) : (fun g => pushForm f n (z g)) ∈ coeffCoboundaries ((binaryFormRepSL R' n).comp Γ.subtype) := by
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hz
  rw [mem_coeffCoboundaries_iff]
  refine ⟨pushForm f n v, funext fun g => ?_⟩
  have h := congrFun hv g
  change binaryFormRepSL R n (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) v - v = z g at h
  show binaryFormRepSL R' n (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (pushForm f n v) - pushForm f n v = pushForm f n (z g)
  rw [← h, pushForm_sub, pushForm_binaryFormRepSL]

noncomputable def pushPar : AddMonoidHom (↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) (↥(coeffParabolicCocycles ((binaryFormRepSL R' n).comp Γ.subtype))) where
  toFun z := ⟨fun g => pushForm f n (z.1 g), pushForm_comp_mem_coeffParabolicCocycles f n z.2⟩
  map_zero' := by
    apply Subtype.ext; funext g
    show pushForm f n ((0 : Γ → ↥(BinaryForm R n)) g) = 0
    rw [Pi.zero_apply, pushForm_zero]
  map_add' z w := by
    apply Subtype.ext; funext g
    show pushForm f n (z.1 g + w.1 g) = pushForm f n (z.1 g) + pushForm f n (w.1 g)
    rw [pushForm_add]

@[simp] private lemma pushPar_apply_coe (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) (g : Γ) : (((pushPar f n z).1 g : ↥(BinaryForm R' n)) : MvPolynomial (Fin 2) R') = pushCoeff f (z.1 g) := rfl

private lemma pushPar_apply_val (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) (g : Γ) : (pushPar f n z).1 g = pushForm f n (z.1 g) := rfl

private lemma mk_eq_mk_iff {S : Type*} [CommRing S] (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))) : coeffH1parMk _ a = coeffH1parMk _ b ↔ ((a - b : ↥(coeffParabolicCocycles ((binaryFormRepSL S n).comp Γ.subtype))).1 ∈ coeffCoboundaries ((binaryFormRepSL S n).comp Γ.subtype)) := by
  rw [← sub_eq_zero, ← map_sub, coeffH1parMk_eq_zero_iff]

private lemma pushPar_sub (a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) : pushPar f n (a - b) = pushPar f n a - pushPar f n b := map_sub (pushPar f n) a b

private lemma mk_pushPar_congr {a b : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))} (h : coeffH1parMk _ a = coeffH1parMk _ b) : coeffH1parMk _ (pushPar f n a) = coeffH1parMk _ (pushPar f n b) := by
  rw [mk_eq_mk_iff] at h ⊢
  rw [← pushPar_sub]
  exact pushForm_comp_mem_coeffCoboundaries f n h

noncomputable def pushH1par : AddMonoidHom (coeffH1par ((binaryFormRepSL R n).comp Γ.subtype)) (coeffH1par ((binaryFormRepSL R' n).comp Γ.subtype)) where
  toFun x := coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) x))
  map_zero' := by
    let z0 := Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype)) 0
    have h0 : coeffH1parMk _ z0 = coeffH1parMk _ (0 : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) := by
      rw [Function.surjInv_eq (coeffH1parMk_surjective _), map_zero]
    show coeffH1parMk _ (pushPar f n z0) = 0
    rw [mk_pushPar_congr f n h0, map_zero, map_zero]
  map_add' x y := by
    let sx := Function.surjInv (coeffH1parMk_surjective ((binaryFormRepSL R n).comp Γ.subtype))
    have hxy : coeffH1parMk _ (sx (x + y)) = coeffH1parMk _ (sx x + sx y) := by
      rw [map_add, Function.surjInv_eq (coeffH1parMk_surjective _), Function.surjInv_eq (coeffH1parMk_surjective _),
        Function.surjInv_eq (coeffH1parMk_surjective _)]
    show coeffH1parMk _ (pushPar f n (sx (x + y))) = _
    rw [mk_pushPar_congr f n hxy, map_add, map_add]

private lemma pushH1par_mk (z : ↥(coeffParabolicCocycles ((binaryFormRepSL R n).comp Γ.subtype))) : pushH1par f n (coeffH1parMk _ z) = coeffH1parMk _ (pushPar f n z) := by
  show coeffH1parMk _ (pushPar f n (Function.surjInv (coeffH1parMk_surjective _) (coeffH1parMk _ z))) = _
  apply mk_pushPar_congr
  exact Function.surjInv_eq (coeffH1parMk_surjective _) _

private lemma pushCoeff_ringHom_eq_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial (Fin 2) R) : pushCoeff φ.toAddMonoidHom P = MvPolynomial.map φ P := by
  ext d
  rw [coeff_pushCoeff, coeff_map]
  rfl

noncomputable abbrev ιQC : AddMonoidHom ℚ ℂ := (algebraMap ℚ ℂ).toAddMonoidHom

noncomputable abbrev BQC := Module.Basis.ofVectorSpace ℚ ℂ

noncomputable abbrev πQC (α : Module.Basis.ofVectorSpaceIndex ℚ ℂ) : AddMonoidHom ℂ ℚ := ((BQC).coord α).toAddMonoidHom

variable (n : ℕ)

private lemma coe_pushForm_ιQC (P : ↥(BinaryForm ℚ n)) : ((pushForm ιQC n P : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = MvPolynomial.map (algebraMap ℚ ℂ) P := by
  rw [coe_pushForm]; exact pushCoeff_ringHom_eq_map _ _

private lemma pushForm_π_smul_ι (α : Module.Basis.ofVectorSpaceIndex ℚ ℂ) (c : ℂ) (Q : ↥(BinaryForm ℚ n)) : pushForm (πQC α) n (c • pushForm ιQC n Q) = (BQC.coord α c) • Q := by
  apply Subtype.ext
  ext d
  simp only [coe_pushForm, coeff_pushCoeff, Submodule.coe_smul, coeff_smul, smul_eq_mul]
  show (BQC.coord α) (c * (algebraMap ℚ ℂ) ((Q : MvPolynomial (Fin 2) ℚ).coeff d)) = _
  rw [mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul, mul_comm]

private lemma sum_smul_pushForm_π (P : ↥(BinaryForm ℂ n)) (A : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ)) (hA : ∀ d ∈ (P : MvPolynomial (Fin 2) ℂ).support, (BQC.repr ((P : MvPolynomial (Fin 2) ℂ).coeff d)).support ⊆ A) : ∑ α ∈ A, (BQC α : ℂ) • pushForm ιQC n (pushForm (πQC α) n P) = P := by
  classical
  apply Subtype.ext
  ext d
  rw [Submodule.coe_sum, coeff_sum]
  simp only [Submodule.coe_smul, coeff_smul, coe_pushForm, coeff_pushCoeff, smul_eq_mul]
  if hd : d ∈ (P : MvPolynomial (Fin 2) ℂ).support then
    set x : ℂ := (P : MvPolynomial (Fin 2) ℂ).coeff d
    have hx := BQC.linearCombination_repr x
    rw [Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset (BQC.repr x) (hA d hd) (fun i a => a • (BQC i : ℂ)) (fun i _ => zero_smul ℚ _)] at hx
    conv_rhs => rw [← hx]
    refine Finset.sum_congr rfl fun α _ => ?_
    show (BQC α : ℂ) * (algebraMap ℚ ℂ) (BQC.coord α x) = (BQC.repr x α) • (BQC α : ℂ)
    rw [Algebra.smul_def, mul_comm]
    rfl
  else
    rw [notMem_support_iff.mp hd]
    refine Finset.sum_eq_zero fun α _ => ?_
    show (BQC α : ℂ) * (algebraMap ℚ ℂ) ((BQC.coord α) (0 : ℂ)) = 0
    rw [map_zero, map_zero, mul_zero]

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}

private lemma exists_eq_sum_smul_pushPar (s : Finset Γ) (hs : Subgroup.closure (s : Set Γ) = ⊤) (Z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype))) : ∃ A : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ), Z = ∑ α ∈ A, (BQC α : ℂ) • pushPar ιQC n (pushPar (πQC α) n Z) := by
  classical
  let A : Finset (Module.Basis.ofVectorSpaceIndex ℚ ℂ) :=
    s.biUnion fun g => ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).support.biUnion fun d =>
      (BQC.repr (((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)).support
  refine ⟨A, Subtype.ext ?_⟩
  set T : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype)) :=
    ∑ α ∈ A, (BQC α : ℂ) • pushPar ιQC n (pushPar (πQC α) n Z) with hT
  refine coeffCocycles_eq_of_eqOn Z.2.1 T.2.1 hs fun g hg => ?_
  rw [hT]
  rw [Submodule.coe_sum, Finset.sum_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, pushPar_apply_val]
  symm
  apply sum_smul_pushForm_π
  intro d hd
  exact Finset.subset_biUnion_of_mem (fun d => (BQC.repr (((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)).support) hd
    |>.trans (Finset.subset_biUnion_of_mem (fun g => ((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).support.biUnion fun d =>
      (BQC.repr (((Z.1 g : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ).coeff d)).support) hg)

variable (Ψ : AddMonoidHom (coeffH1par ((binaryFormRepSL ℚ n).comp Γ.subtype)) (coeffH1par ((binaryFormRepSL ℂ n).comp Γ.subtype))) (hΨ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℚ n).comp Γ.subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype)), (∀ g : Γ, ((w : Γ → ↥(BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ) = MvPolynomial.map (algebraMap ℚ ℂ) (((z : Γ → ↥(BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ))) ∧ Ψ (coeffH1parMk _ z) = coeffH1parMk _ w)

include hΨ in
private lemma Ψ_mk (z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℚ n).comp Γ.subtype))) : Ψ (coeffH1parMk _ z) = coeffH1parMk _ (pushPar ιQC n z) := by
  obtain ⟨w, hw, h⟩ := hΨ z
  rw [h]
  congr 1
  apply Subtype.ext; funext g; apply Subtype.ext
  rw [hw g]
  exact (coe_pushForm_ιQC n _).symm

include hΨ in
private lemma mem_span_range (s : Finset Γ) (hs : Subgroup.closure (s : Set Γ) = ⊤) (X : coeffH1par ((binaryFormRepSL ℂ n).comp Γ.subtype)) : X ∈ Submodule.span ℂ (Set.range Ψ) := by
  classical
  obtain ⟨Z, rfl⟩ := coeffH1parMk_surjective _ X
  obtain ⟨A, hA⟩ := exists_eq_sum_smul_pushPar n s hs Z
  rw [hA, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨coeffH1parMk _ (pushPar (πQC α) n Z), ?_⟩)
  exact Ψ_mk n Ψ hΨ _

include hΨ in
private lemma linearIndependent_comp {ι : Type*} (y : ι → coeffH1par ((binaryFormRepSL ℚ n).comp Γ.subtype)) (hy : LinearIndependent ℚ y) : LinearIndependent ℂ (fun i => Ψ (y i)) := by
  classical
  rw [linearIndependent_iff'] at hy ⊢
  intro t c hc i hi
  choose Y hY using fun i => coeffH1parMk_surjective ((binaryFormRepSL ℚ n).comp Γ.subtype) (y i)
  have hΨy : ∀ i, Ψ (y i) = coeffH1parMk _ (pushPar ιQC n (Y i)) := fun i => by rw [← hY i, Ψ_mk n Ψ hΨ]
  simp only [hΨy] at hc
  simp only [← LinearMap.map_smul (coeffH1parMk ((binaryFormRepSL ℂ n).comp Γ.subtype)), ← map_sum] at hc
  rw [coeffH1parMk_eq_zero_iff] at hc
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hc
  suffices hcoord : ∀ α, BQC.coord α (c i) = 0 from (BQC.forall_coord_eq_zero_iff).mp hcoord
  intro α
  apply hy t (fun j => BQC.coord α (c j)) _ i hi
  ·
    have hrel : (∑ j ∈ t, (BQC.coord α (c j)) • (Y j : Γ → ↥(BinaryForm ℚ n))) ∈
      coeffCoboundaries ((binaryFormRepSL ℚ n).comp Γ.subtype) := by
      rw [mem_coeffCoboundaries_iff]
      refine ⟨pushForm (πQC α) n v, funext fun g => ?_⟩
      have h1 := congrFun hv g
      change binaryFormRepSL ℂ n (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) v - v = _ at h1
      show binaryFormRepSL ℚ n (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (pushForm (πQC α) n v) - pushForm (πQC α) n v = _
      rw [← pushForm_binaryFormRepSL, ← pushForm_sub, h1, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
      have hadd : ∀ (F : Finset ι) (G : ι → ↥(BinaryForm ℂ n)),
        pushForm (πQC α) n (∑ j ∈ F, G j) = ∑ j ∈ F, pushForm (πQC α) n (G j) := by
        intro F G
        exact map_sum (⟨⟨pushForm (πQC α) n, pushForm_zero _ n⟩, pushForm_add _ n⟩ : AddMonoidHom ↥(BinaryForm ℂ n) ↥(BinaryForm ℚ n)) G F
      rw [hadd]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, Pi.smul_apply, pushPar_apply_val, pushForm_π_smul_ι]
      rfl
    have : (∑ j ∈ t, (BQC.coord α (c j)) • y j) = coeffH1parMk ((binaryFormRepSL ℚ n).comp Γ.subtype) (∑ j ∈ t, (BQC.coord α (c j)) • Y j) := by
      rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_smul, hY]
    rw [this, coeffH1parMk_eq_zero_iff]
    simpa [Submodule.coe_sum, Submodule.coe_smul] using hrel

omit hΨ in
/--
[HeckeEis_mem_span_range_coeffH1par_map_rat_complex](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HeckeEis_mem_span_range_coeffH1par_map_rat_complex.lean)
-/
@[path]
private lemma main
  {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Group.FG Γ]
  {n : ℕ}
  {Ψ : AddMonoidHom (coeffH1par ((binaryFormRepSL ℚ n).comp Γ.subtype))
    (coeffH1par ((binaryFormRepSL ℂ n).comp Γ.subtype))}
  {X : coeffH1par ((binaryFormRepSL ℂ n).comp Γ.subtype)}
-- given
  (hΨ : ∀ z : ↥(coeffParabolicCocycles ((binaryFormRepSL ℚ n).comp Γ.subtype)), ∃ w : ↥(coeffParabolicCocycles ((binaryFormRepSL ℂ n).comp Γ.subtype)), (∀ g : Γ, ((w : Γ → ↥(BinaryForm ℂ n)) g : MvPolynomial (Fin 2) ℂ) = MvPolynomial.map (algebraMap ℚ ℂ) (((z : Γ → ↥(BinaryForm ℚ n)) g : MvPolynomial (Fin 2) ℚ))) ∧ Ψ (coeffH1parMk _ z) = coeffH1parMk _ w) :
-- imply
  X ∈ Submodule.span ℂ (Set.range Ψ) := by
-- proof
  obtain ⟨S, hS⟩ := Group.fg_def.mp (inferInstance : Group.FG Γ)
  exact mem_span_range n Ψ hΨ S hS X


-- created on 2026-10-23
-- updated on 2026-10-26
