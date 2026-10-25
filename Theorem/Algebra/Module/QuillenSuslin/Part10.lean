/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Ring
import Def.Algebra.Module.QuillenSuslin.Part10
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qs_exists_lifts_after_scale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S]
    {a : Type*} [Finite a]
    (p : a → Polynomial S) (hzero : ∀ i, (p i).coeff 0 = 0) :
    ∃ b : M, ∀ i, ∃ q : Polynomial R,
      q.map (algebraMap R S) =
        (p i).comp (Polynomial.C (algebraMap R S b) * Polynomial.X) := by
  classical
  let _ : Fintype a := Fintype.ofFinite a
  let I := Σ i : a, {n // n ∈ (p i).support}
  let f : I → S := fun z ↦ (p z.1).coeff z.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M f
  refine ⟨b, fun i ↦ ?_⟩
  have hlift :
      (p i).comp (Polynomial.C (algebraMap R S b) * Polynomial.X) ∈
        Polynomial.lifts (algebraMap R S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.comp_C_mul_X_coeff]
    by_cases hn0 : n = 0
    · subst n
      rw [hzero i, zero_mul]
      exact ⟨0, map_zero _⟩
    by_cases hn : n ∈ (p i).support
    · have hi := hb ⟨i, ⟨n, hn⟩⟩
      rw [Algebra.smul_def] at hi
      obtain ⟨c, hc⟩ := hi
      change algebraMap R S c =
        algebraMap R S (b : R) * (p i).coeff n at hc
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      refine ⟨c * (b : R) ^ d, ?_⟩
      rw [map_mul, map_pow, hc]
      rw [pow_succ]
      ring
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact ⟨0, by simp⟩
  exact (Polynomial.lifts_iff_set_range _).mp hlift

theorem qs_constantCoeff_comp_shear_one
    {R : Type*} [CommRing R] :
    (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp
        (qsShear (1 : R)) =
      (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp
        Polynomial.C := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShear]
  · simp [qsShear]

theorem qs_constantCoeff_comp_shear_one_eq_id
    {R : Type*} [CommRing R] :
    (Polynomial.constantCoeff : Polynomial (Polynomial R) →+* Polynomial R).comp
        (qsShear (1 : R)) = RingHom.id (Polynomial R) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShear]
  · simp [qsShear]

theorem qs_exists_transition_with_zero_constant
    {R : Type*} [CommRing R]
    {i k : Type*} [Fintype i] [Fintype k] [DecidableEq k]
    {E : Matrix i i (Polynomial R)}
    (h : qsMatrixEquiv E (1 : Matrix k k (Polynomial R))) :
    ∃ C D : Matrix i i (Polynomial (Polynomial R)),
      C * D = E.map (qsShear (1 : R)) ∧
      D * C = E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) ∧
      (∀ x y, (C x y - Polynomial.C (E x y)).coeff 0 = 0) ∧
      ∀ x y, (D x y - Polynomial.C (E x y)).coeff 0 = 0 := by
  obtain ⟨C, D, hCD, hDC, hC0, hD0⟩ :=
    qs_transition_one_of_equal_after h (qsShear (1 : R)) Polynomial.C
      Polynomial.constantCoeff qs_constantCoeff_comp_shear_one
  rw [qs_constantCoeff_comp_shear_one_eq_id] at hC0 hD0
  refine ⟨C, D, hCD, hDC, ?_, ?_⟩
  · intro x y
    have hxy := congrFun (congrFun hC0 x) y
    simpa [Polynomial.coeff_zero_eq_eval_zero] using sub_eq_zero.mpr hxy
  · intro x y
    have hxy := congrFun (congrFun hD0 x) y
    simpa [Polynomial.coeff_zero_eq_eval_zero] using sub_eq_zero.mpr hxy

theorem qs_patching_member_of_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {M : Submonoid R} [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R)
    {i k : Type*} [Fintype i] [Fintype k] [DecidableEq k]
    (E : Matrix i i (Polynomial R)) (hE : E * E = E)
    (hlocal : qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (algebraMap R S)))
      (1 : Matrix k k (Polynomial S))) :
    ∃ r : M, (r : R) ∈ qsPatchingIdeal E hE := by
  classical
  let f : Polynomial R →+* Polynomial S :=
    Polynomial.mapRingHom (algebraMap R S)
  obtain ⟨C, D, hCD, hDC, hCzero, hDzero⟩ :=
    qs_exists_transition_with_zero_constant hlocal
  let _ : Algebra (Polynomial R) (Polynomial S) := Polynomial.algebra R S
  let _ : IsLocalization (M.map Polynomial.C) (Polynomial S) :=
    Polynomial.isLocalization M S
  let p : Bool × (i × i) → Polynomial (Polynomial S) := fun z ↦
    match z.1 with
    | true => C z.2.1 z.2.2 - Polynomial.C (f (E z.2.1 z.2.2))
    | false => D z.2.1 z.2.2 - Polynomial.C (f (E z.2.1 z.2.2))
  have hpzero : ∀ z, (p z).coeff 0 = 0 := by
    rintro ⟨b, x, y⟩
    cases b
    · simpa [p, f] using hDzero x y
    · simpa [p, f] using hCzero x y
  obtain ⟨b, hb⟩ := qs_exists_lifts_after_scale
    (R := Polynomial R) (S := Polynomial S) (M := M.map Polynomial.C) p hpzero
  obtain ⟨r, hr, hCr⟩ := Submonoid.mem_map.mp b.property
  let qC : Matrix i i (Polynomial (Polynomial R)) := fun x y ↦
    Classical.choose (hb (true, (x, y)))
  let qD : Matrix i i (Polynomial (Polynomial R)) := fun x y ↦
    Classical.choose (hb (false, (x, y)))
  let E₀ : Matrix i i (Polynomial (Polynomial R)) := E.map Polynomial.C
  let C₀ := E₀ + qC
  let D₀ := E₀ + qD
  let F : Polynomial (Polynomial R) →+* Polynomial (Polynomial S) :=
    Polynomial.mapRingHom f
  let scale : Polynomial (Polynomial S) →+* Polynomial (Polynomial S) :=
    qsScaleY (algebraMap R S r)
  have hCmap : C₀.map F = C.map scale := by
    apply Matrix.ext
    intro x y
    have hq := Classical.choose_spec (hb (true, (x, y)))
    change F (C₀ x y) = scale (C x y)
    change F (E₀ x y + qC x y) = scale (C x y)
    rw [map_add]
    change F (Polynomial.C (E x y)) + F (qC x y) = scale (C x y)
    change F (Polynomial.C (E x y)) +
      (qC x y).map (algebraMap (Polynomial R) (Polynomial S)) = scale (C x y)
    rw [hq]
    simp only [p]
    rw [← hCr]
    simp [F, f, scale, qsScaleY, Polynomial.comp]
  have hDmap : D₀.map F = D.map scale := by
    apply Matrix.ext
    intro x y
    have hq := Classical.choose_spec (hb (false, (x, y)))
    change F (D₀ x y) = scale (D x y)
    change F (E₀ x y + qD x y) = scale (D x y)
    rw [map_add]
    change F (Polynomial.C (E x y)) + F (qD x y) = scale (D x y)
    change F (Polynomial.C (E x y)) +
      (qD x y).map (algebraMap (Polynomial R) (Polynomial S)) = scale (D x y)
    rw [hq]
    simp only [p]
    rw [← hCr]
    simp [F, f, scale, qsScaleY, Polynomial.comp]
  refine ⟨⟨r, hr⟩, ?_⟩
  change qsMatrixEquiv (E.map (qsShear r)) E₀
  refine ⟨C₀, D₀, ?_, ?_⟩
  · apply Matrix.map_injective (Polynomial.map_injective f <|
      Polynomial.map_injective (algebraMap R S) (IsLocalization.injective S hM))
    change (C₀ * D₀).map F = (E.map (qsShear r)).map F
    rw [Matrix.map_mul, hCmap, hDmap, ← Matrix.map_mul, hCD]
    apply Matrix.ext
    intro x y
    simpa [F, f, scale] using
      DFunLike.congr_fun (qs_scale_shear_map (algebraMap R S) r) (E x y)
  · apply Matrix.map_injective (Polynomial.map_injective f <|
      Polynomial.map_injective (algebraMap R S) (IsLocalization.injective S hM))
    change (D₀ * C₀).map F = E₀.map F
    rw [Matrix.map_mul, hDmap, hCmap, ← Matrix.map_mul, hDC]
    apply Matrix.ext
    intro x y
    simp [F, f, scale, qsScaleY, E₀]

theorem qs_quillen_patching
    {R : Type*} [CommRing R] [IsDomain R]
    {i : Type*} [Fintype i]
    (E : Matrix i i (Polynomial R)) (hE : E * E = E)
    (hlocal : ∀ (m : Ideal R) (hm : m.IsMaximal),
      let _ : m.IsPrime := hm.isPrime
      ∃ n : ℕ, qsMatrixEquiv
        (E.map (Polynomial.mapRingHom (algebraMap R (Localization.AtPrime m))))
        (1 : Matrix (Fin n) (Fin n) (Polynomial (Localization.AtPrime m)))) :
    qsMatrixEquiv E (E.map (qsConstantAtZero : Polynomial R →+* Polynomial R)) := by
  let J := qsPatchingIdeal E hE
  have hJtop : J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hne
    let _ : m.IsPrime := hm.isPrime
    obtain ⟨n, hn⟩ := hlocal m hm
    obtain ⟨r, hr⟩ := qs_patching_member_of_localization
      (S := Localization.AtPrime m) (M := m.primeCompl)
      m.primeCompl_le_nonZeroDivisors E hE hn
    exact r.property (hJm hr)
  have h1 : (1 : R) ∈ J := by
    rw [hJtop]
    simp
  have hmapped := h1.map (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R)
  change qsMatrixEquiv
    (E.map ((qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
      (qsShear (1 : R))))
    (E.map ((qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
      Polynomial.C)) at hmapped
  rw [qsEvalXY_comp_shear_one, qsEvalXY_comp_C] at hmapped
  have hid : E.map (RingHom.id (Polynomial R)) = E := by
    rfl
  rw [hid] at hmapped
  exact hmapped

theorem qs_range_projective
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι R) (hE : E * E = E) :
    Module.Projective R (LinearMap.range E.mulVecLin) := by
  let p := E.mulVecLin
  apply Module.Projective.of_split (LinearMap.range p).subtype p.rangeRestrict
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change p x = x
  rw [← hy]
  change E.mulVecLin (E.mulVecLin y) = E.mulVecLin y
  change (E.mulVecLin.comp E.mulVecLin) y = E.mulVecLin y
  rw [← Matrix.mulVecLin_mul, hE]

theorem qs_range_finite
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι R) :
    Module.Finite R (LinearMap.range E.mulVecLin) :=
  Module.Finite.range E.mulVecLin

theorem qs_mulVec_eq_self_of_mem_range
    {R : Type*} [CommRing R]
    {ι : Type*} [Fintype ι]
    {E : Matrix ι ι R} (hE : E * E = E)
    {x : ι → R} (hx : x ∈ LinearMap.range E.mulVecLin) :
    E.mulVecLin x = x := by
  obtain ⟨y, rfl⟩ := hx
  change (E.mulVecLin.comp E.mulVecLin) y = E.mulVecLin y
  rw [← Matrix.mulVecLin_mul, hE]

theorem qs_equiv_one_of_free_range
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (E : Matrix ι ι R) (hE : E * E = E)
    [Module.Free R (LinearMap.range E.mulVecLin)]
    [Module.Finite R (LinearMap.range E.mulVecLin)] :
    ∃ (κ : Type (max u v)) (_ : Fintype κ) (_ : DecidableEq κ),
      qsMatrixEquiv E (1 : Matrix κ κ R) := by
  classical
  let P := LinearMap.range E.mulVecLin
  let κ := Module.Free.ChooseBasisIndex R P
  let _ : Fintype κ := Module.Free.ChooseBasisIndex.fintype R P
  let b := Module.Free.chooseBasis R P
  let e := Finsupp.linearEquivFunOnFinite R R κ
  let a : (κ → R) →ₗ[R] (ι → R) :=
    (LinearMap.range E.mulVecLin).subtype.comp
      (b.repr.symm.toLinearMap.comp e.symm.toLinearMap)
  let c : (ι → R) →ₗ[R] (κ → R) :=
    e.toLinearMap.comp (b.repr.toLinearMap.comp E.mulVecLin.rangeRestrict)
  refine ⟨κ, inferInstance, inferInstance, LinearMap.toMatrix' a, LinearMap.toMatrix' c, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_toLin' E]
    congr 1
    ext x
    simp only [a, c, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, Submodule.coe_subtype]
    rfl
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro x
    let z : P := b.repr.symm (e.symm x)
    have hz : E.mulVecLin.rangeRestrict (z : ι → R) = z := by
      apply Subtype.ext
      exact qs_mulVec_eq_self_of_mem_range hE z.property
    change e (b.repr (E.mulVecLin.rangeRestrict (z : ι → R))) = x
    rw [hz]
    simp [z]

theorem qs_equiv_one_fin_of_free_range
    {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι]
    (E : Matrix ι ι R) (hE : E * E = E)
    [Module.Free R (LinearMap.range E.mulVecLin)]
    [Module.Finite R (LinearMap.range E.mulVecLin)] :
    ∃ n : ℕ, qsMatrixEquiv E (1 : Matrix (Fin n) (Fin n) R) := by
  classical
  obtain ⟨κ, _, _, hκ⟩ := qs_equiv_one_of_free_range E hE
  exact ⟨Fintype.card κ,
    hκ.reindex_one (Fintype.equivFin κ).symm⟩

theorem qs_residue_equiv_one
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E) :
    ∃ n : ℕ, qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (IsLocalRing.residue R)))
      (1 : Matrix (Fin n) (Fin n)
        (Polynomial (IsLocalRing.ResidueField R))) := by
  let Ebar := E.map (Polynomial.mapRingHom (IsLocalRing.residue R))
  have hEbar : Ebar * Ebar = Ebar := qs_idempotent_map hE _
  let _ : Module.Projective (Polynomial (IsLocalRing.ResidueField R))
      (LinearMap.range Ebar.mulVecLin) := qs_range_projective Ebar hEbar
  let _ : Module.Finite (Polynomial (IsLocalRing.ResidueField R))
      (LinearMap.range Ebar.mulVecLin) := qs_range_finite Ebar
  let _ : Module.Free (Polynomial (IsLocalRing.ResidueField R))
      (LinearMap.range Ebar.mulVecLin) :=
    Module.free_of_finite_type_torsion_free'
  exact qs_equiv_one_fin_of_free_range Ebar hEbar

theorem qs_fin_eq_of_one_equiv_one
    {K : Type*} [Field K] {n m : ℕ}
    (h : qsMatrixEquiv (1 : Matrix (Fin n) (Fin n) K)
      (1 : Matrix (Fin m) (Fin m) K)) : n = m := by
  classical
  obtain ⟨A, B, hAB, hBA⟩ := h
  let e : (Fin m → K) ≃ₗ[K] (Fin n → K) :=
    LinearEquiv.ofLinearMap A.mulVecLin B.mulVecLin (by
      apply LinearMap.ext
      intro x
      change (A.mulVecLin.comp B.mulVecLin) x = x
      rw [← Matrix.mulVecLin_mul, hAB, Matrix.mulVecLin_one,
        LinearMap.id_apply]) (by
      apply LinearMap.ext
      intro x
      change (B.mulVecLin.comp A.mulVecLin) x = x
      rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one,
        LinearMap.id_apply])
  have hrank := e.finrank_eq
  rw [Module.finrank_eq_card_basis (Pi.basisFun K (Fin m)),
    Module.finrank_eq_card_basis (Pi.basisFun K (Fin n)),
    Fintype.card_fin, Fintype.card_fin] at hrank
  exact hrank.symm

theorem qs_residue_equiv_one_same_rank
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E)
    {m : ℕ}
    (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
    qsMatrixEquiv
      (E.map (Polynomial.mapRingHom (IsLocalRing.residue R)))
      (1 : Matrix (Fin m) (Fin m)
        (Polynomial (IsLocalRing.ResidueField R))) := by
  classical
  obtain ⟨n, hn⟩ := qs_residue_equiv_one R E hE
  let k := IsLocalRing.ResidueField R
  let K := Localization (qsMonicSubmonoid k)
  let Q := Localization (qsMonicSubmonoid R)
  let _ : IsFractionRing (Polynomial k) K :=
    qs_monicLocalization_isFractionRing k
  let _ : Field K := IsFractionRing.toField (Polynomial k)
  have hnK := hn.map (algebraMap (Polynomial k) K)
  have hmK := hQ.map (qsResidueMonicMap R)
  rw [Matrix.map_one (algebraMap (Polynomial k) K) (map_zero _) (map_one _)] at hnK
  rw [Matrix.map_one (qsResidueMonicMap R) (map_zero _) (map_one _)] at hmK
  have hcompat :
      (E.map (algebraMap (Polynomial R) Q)).map (qsResidueMonicMap R) =
        (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))).map
          (algebraMap (Polynomial k) K) := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (E i j)
  rw [hcompat] at hmK
  have hone : qsMatrixEquiv (1 : Matrix (Fin n) (Fin n) K)
      (1 : Matrix (Fin m) (Fin m) K) :=
    hnK.symm.trans hmK (by simp) (by simp)
  have hnm : n = m := qs_fin_eq_of_one_equiv_one hone
  subst n
  exact hn

end QuillenSuslin
