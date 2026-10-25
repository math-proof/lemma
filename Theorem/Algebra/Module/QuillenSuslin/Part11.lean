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
import Def.Algebra.Module.QuillenSuslin.Part11
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qs_horrocks_adjusted_factors
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E)
    {m : ℕ}
    (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
    ∃ A : Matrix ι (Fin m) (Localization (qsMonicSubmonoid R)),
      ∃ B : Matrix (Fin m) ι (Localization (qsMonicSubmonoid R)),
        A * B = E.map (algebraMap (Polynomial R)
          (Localization (qsMonicSubmonoid R))) ∧
        B * A = 1 ∧
        qsResiduePolynomialMatrix R A ∧
        qsResiduePolynomialMatrix R B := by
  classical
  let k := IsLocalRing.ResidueField R
  let K := Localization (qsMonicSubmonoid k)
  let Q := Localization (qsMonicSubmonoid R)
  let q : Q →+* K := qsResidueMonicMap R
  let ak : Polynomial k →+* K := algebraMap (Polynomial k) K
  let _ : IsFractionRing (Polynomial k) K :=
    qs_monicLocalization_isFractionRing k
  let _ : Field K := IsFractionRing.toField (Polynomial k)
  obtain ⟨C, D, hCD, hDC⟩ :=
    qs_residue_equiv_one_same_rank R E hE hQ
  obtain ⟨A, B, hAB, hBA⟩ := hQ
  let AK := A.map q
  let BK := B.map q
  let CK := C.map ak
  let DK := D.map ak
  have hcompat :
      (E.map (algebraMap (Polynomial R) Q)).map q =
        (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (E i j)
  have hABK : AK * BK = CK * DK := by
    calc
      AK * BK = (A * B).map q := by simp only [AK, BK, Matrix.map_mul]
      _ = (E.map (algebraMap (Polynomial R) Q)).map q := by rw [hAB]
      _ = (E.map (Polynomial.mapRingHom (IsLocalRing.residue R))).map ak := hcompat
      _ = (C * D).map ak := by rw [hCD]
      _ = CK * DK := by simp only [CK, DK, Matrix.map_mul]
  have hBAK : BK * AK = 1 := by
    calc
      BK * AK = (B * A).map q := by simp only [AK, BK, Matrix.map_mul]
      _ = (1 : Matrix (Fin m) (Fin m) Q).map q := by rw [hBA]
      _ = 1 := Matrix.map_one q q.map_zero q.map_one
  have hDCK : DK * CK = 1 := by
    calc
      DK * CK = (D * C).map ak := by simp only [CK, DK, Matrix.map_mul]
      _ = (1 : Matrix (Fin m) (Fin m) (Polynomial k)).map ak := by rw [hDC]
      _ = 1 := Matrix.map_one ak ak.map_zero ak.map_one
  let T := DK * AK
  let S := BK * CK
  have hTS : T * S = 1 := by
    calc
      T * S = DK * (AK * BK) * CK := by simp only [T, S, Matrix.mul_assoc]
      _ = DK * (CK * DK) * CK := by rw [hABK]
      _ = (DK * CK) * (DK * CK) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hDCK, Matrix.one_mul]
  have hST : S * T = 1 := by
    calc
      S * T = BK * (CK * DK) * AK := by simp only [S, T, Matrix.mul_assoc]
      _ = BK * (AK * BK) * AK := by rw [← hABK]
      _ = (BK * AK) * (BK * AK) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBAK, Matrix.one_mul]
  have hTdet : T.det ≠ 0 := by
    intro hzero
    have hdet := congrArg Matrix.det hTS
    rw [Matrix.det_mul, hzero, zero_mul, Matrix.det_one] at hdet
    exact zero_ne_one hdet
  obtain ⟨U, hUunit, hUmap⟩ :=
    qs_lift_residue_invertible_matrix R T hTdet
  let Uinv := U⁻¹
  have hleft : T * Uinv.map q = 1 := by
    have hu := congrArg (fun N ↦ N.map q) (Matrix.mul_nonsing_inv U hUunit)
    rw [Matrix.map_mul, hUmap,
      Matrix.map_one q q.map_zero q.map_one] at hu
    exact hu
  have hUinvmap : Uinv.map q = S := by
    calc
      Uinv.map q = 1 * Uinv.map q := by rw [Matrix.one_mul]
      _ = (S * T) * Uinv.map q := by rw [hST]
      _ = S * (T * Uinv.map q) := by rw [Matrix.mul_assoc]
      _ = S := by rw [hleft, Matrix.mul_one]
  let A' := A * Uinv
  let B' := U * B
  have hA'B' : A' * B' = E.map (algebraMap (Polynomial R) Q) := by
    calc
      A' * B' = A * (Uinv * U) * B := by simp only [A', B', Matrix.mul_assoc]
      _ = A * (1 : Matrix (Fin m) (Fin m) Q) * B := by
        rw [Matrix.nonsing_inv_mul U hUunit]
      _ = _ := by rw [Matrix.mul_one, hAB]
  have hB'A' : B' * A' = 1 := by
    calc
      B' * A' = U * (B * A) * Uinv := by simp only [A', B', Matrix.mul_assoc]
      _ = U * 1 * Uinv := by rw [hBA]
      _ = 1 := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv U hUunit]
  have hA'map : A'.map q = CK := by
    calc
      A'.map q = AK * Uinv.map q := by
        simp only [A', AK, Matrix.map_mul]
      _ = AK * (BK * CK) := by rw [hUinvmap]
      _ = (AK * BK) * CK := by rw [Matrix.mul_assoc]
      _ = (CK * DK) * CK := by rw [hABK]
      _ = CK * (DK * CK) := by rw [Matrix.mul_assoc]
      _ = CK := by rw [hDCK, Matrix.mul_one]
  have hB'map : B'.map q = DK := by
    calc
      B'.map q = U.map q * BK := by
        simp only [B', BK, Matrix.map_mul]
      _ = (DK * AK) * BK := by rw [hUmap]
      _ = DK * (AK * BK) := by rw [Matrix.mul_assoc]
      _ = DK * (CK * DK) := by rw [hABK]
      _ = (DK * CK) * DK := by rw [Matrix.mul_assoc]
      _ = DK := by rw [hDCK, Matrix.one_mul]
  exact ⟨A', B', hA'B', hB'A', ⟨C, hA'map⟩, ⟨D, hB'map⟩⟩

theorem qs_horrocks_local
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (Polynomial R)) (hE : E * E = E)
    {m : ℕ}
    (hQ : qsMatrixEquiv
      (E.map (algebraMap (Polynomial R)
        (Localization (qsMonicSubmonoid R))))
      (1 : Matrix (Fin m) (Fin m)
        (Localization (qsMonicSubmonoid R)))) :
    qsMatrixEquiv E (1 : Matrix (Fin m) (Fin m) (Polynomial R)) := by
  classical
  let k := IsLocalRing.ResidueField R
  let Q := Localization (qsMonicSubmonoid R)
  let K := Localization (qsMonicSubmonoid k)
  let alg : Polynomial R →+* Q := algebraMap (Polynomial R) Q
  let ak : Polynomial k →+* K := algebraMap (Polynomial k) K
  let q : Q →+* K := qsResidueMonicMap R
  let bar : Polynomial R →+* Polynomial k :=
    Polynomial.mapRingHom (IsLocalRing.residue R)
  obtain ⟨A, B, hAB, hBA, hA, hB⟩ :=
    qs_horrocks_adjusted_factors R E hE hQ
  obtain ⟨F, hF⟩ := qs_horrocks_map_surjective R A B hBA hA hB
    (1 : Matrix (Fin m) (Fin m) (Polynomial R))
  let FQ := F.map alg
  let H := FQ * A
  have hHpart : qsMatrixPolynomialPart R H = 1 := by
    simpa only [qsHorrocksMap_apply] using hF
  have hHunit : IsUnit H.det :=
    qs_isUnit_det_of_matrixPolynomialPart_eq_one H fun i j ↦
      congrFun (congrFun hHpart i) j
  let Hinv := H⁻¹
  let A₂ := A * Hinv
  let B₂ := H * B
  have hA₂B₂ : A₂ * B₂ = E.map alg := by
    calc
      A₂ * B₂ = A * (Hinv * H) * B := by
        simp only [A₂, B₂, Matrix.mul_assoc]
      _ = A * (1 : Matrix (Fin m) (Fin m) Q) * B := by
        rw [Matrix.nonsing_inv_mul H hHunit]
      _ = E.map alg := by rw [Matrix.mul_one A, hAB]
  have hB₂A₂ : B₂ * A₂ = 1 := by
    calc
      B₂ * A₂ = H * (B * A) * Hinv := by
        simp only [A₂, B₂, Matrix.mul_assoc]
      _ = H * (1 : Matrix (Fin m) (Fin m) Q) * Hinv := by rw [hBA]
      _ = 1 := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv H hHunit]
  let B₀ := F * E
  have hB₂ : B₂ = B₀.map alg := by
    calc
      B₂ = (FQ * A) * B := rfl
      _ = FQ * (A * B) := by rw [Matrix.mul_assoc]
      _ = FQ * E.map alg := by rw [hAB]
      _ = B₀.map alg := by simp only [B₀, FQ, Matrix.map_mul]
  obtain ⟨C, hAC⟩ := hA
  have hFcompat : FQ.map q = (F.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (F i j)
  have hHC : H.map q = (F.map bar * C).map ak := by
    calc
      H.map q = FQ.map q * A.map q := by
        simp only [H, Matrix.map_mul]
      _ = (F.map bar).map ak * C.map ak := by rw [hFcompat, hAC]
      _ = (F.map bar * C).map ak := (Matrix.map_mul ..).symm
  have hFC : F.map bar * C = 1 := by
    have hp := qsMatrixPolynomialPart_map_residue R H (F.map bar * C) hHC
    rw [hHpart] at hp
    calc
      F.map bar * C =
          (1 : Matrix (Fin m) (Fin m) (Polynomial R)).map bar := hp.symm
      _ = 1 := Matrix.map_one bar bar.map_zero bar.map_one
  have hHq : H.map q = 1 := by
    rw [hHC, hFC]
    exact Matrix.map_one ak ak.map_zero ak.map_one
  have hHinvq : Hinv.map q = 1 := by
    have hu := congrArg (fun X ↦ X.map q) (Matrix.mul_nonsing_inv H hHunit)
    rw [Matrix.map_mul, hHq, Matrix.one_mul,
      Matrix.map_one q q.map_zero q.map_one] at hu
    exact hu
  have hA₂res : qsResiduePolynomialMatrix R A₂ := by
    refine ⟨C, ?_⟩
    calc
      A₂.map q = A.map q * Hinv.map q := by
        simp only [A₂, Matrix.map_mul]
      _ = C.map ak * (1 : Matrix (Fin m) (Fin m) K) := by
        rw [hAC, hHinvq]
      _ = C.map ak := Matrix.mul_one _
  have hB₀compat : (B₀.map alg).map q = (B₀.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (B₀ i j)
  have hB₂res : qsResiduePolynomialMatrix R B₂ := by
    refine ⟨B₀.map bar, ?_⟩
    rw [hB₂]
    exact hB₀compat
  obtain ⟨C₂, hB₂C₂⟩ := hB₂res
  obtain ⟨D₂, hA₂D₂⟩ := hA₂res
  have htransinv : A₂.transpose * B₂.transpose = 1 := by
    rw [← Matrix.transpose_mul, hB₂A₂, Matrix.transpose_one]
  have hB₂transres : qsResiduePolynomialMatrix R B₂.transpose := by
    refine ⟨C₂.transpose, ?_⟩
    rw [Matrix.transpose_map, hB₂C₂, Matrix.transpose_map]
  have hA₂transres : qsResiduePolynomialMatrix R A₂.transpose := by
    refine ⟨D₂.transpose, ?_⟩
    rw [Matrix.transpose_map, hA₂D₂, Matrix.transpose_map]
  obtain ⟨F₂, hF₂⟩ := qs_horrocks_map_surjective R
    B₂.transpose A₂.transpose htransinv hB₂transres hA₂transres
    (1 : Matrix (Fin m) (Fin m) (Polynomial R))
  have hF₂part : qsMatrixPolynomialPart R
      (F₂.map alg * B₂.transpose) = 1 := by
    simpa only [qsHorrocksMap_apply] using hF₂
  let G := F₂.transpose
  have htrans : (F₂.map alg * B₂.transpose).transpose =
      B₂ * G.map alg := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map]
  have hBGpart : qsMatrixPolynomialPart R (B₂ * G.map alg) = 1 := by
    have hp := congrArg Matrix.transpose hF₂part
    rw [← qsMatrixPolynomialPart_transpose, htrans, Matrix.transpose_one] at hp
    exact hp
  have hB₀G : B₀ * G = 1 := by
    calc
      B₀ * G = qsMatrixPolynomialPart R ((B₀ * G).map alg) :=
        (qsMatrixPolynomialPart_algebraMap (B₀ * G)).symm
      _ = qsMatrixPolynomialPart R (B₂ * G.map alg) := by
        rw [Matrix.map_mul, ← hB₂]
      _ = 1 := hBGpart
  let A₀ := E * G
  have hA₂ : A₂ = A₀.map alg := by
    calc
      A₂ = A₂ * (1 : Matrix (Fin m) (Fin m) Q) := (Matrix.mul_one A₂).symm
      _ = A₂ * ((B₀ * G).map alg) := by
        rw [hB₀G, Matrix.map_one alg alg.map_zero alg.map_one]
      _ = A₂ * (B₂ * G.map alg) := by rw [Matrix.map_mul, ← hB₂]
      _ = (A₂ * B₂) * G.map alg := (Matrix.mul_assoc ..).symm
      _ = E.map alg * G.map alg := by rw [hA₂B₂]
      _ = A₀.map alg := by simp only [A₀, Matrix.map_mul]
  have halg : Function.Injective alg :=
    IsLocalization.injective Q fun _
      (hs : _ ∈ qsMonicSubmonoid R) ↦
        Polynomial.Monic.mem_nonZeroDivisors hs
  refine ⟨A₀, B₀, ?_, ?_⟩
  · apply Matrix.map_injective halg
    calc
      (A₀ * B₀).map alg = A₂ * B₂ := by rw [Matrix.map_mul, ← hA₂, ← hB₂]
      _ = E.map alg := hA₂B₂
  · apply Matrix.map_injective halg
    calc
      (B₀ * A₀).map alg = B₂ * A₂ := by rw [Matrix.map_mul, ← hA₂, ← hB₂]
      _ = 1 := hB₂A₂
      _ = (1 : Matrix (Fin m) (Fin m) (Polynomial R)).map alg :=
        (Matrix.map_one alg alg.map_zero alg.map_one).symm

theorem qs_free_range_of_equiv_one
    {R : Type*} [CommRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {E : Matrix ι ι R}
    (h : qsMatrixEquiv E (1 : Matrix κ κ R)) :
    Module.Free R (LinearMap.range E.mulVecLin) := by
  classical
  obtain ⟨A, B, hAB, hBA⟩ := h
  have hE : E * E = E := by
    calc
      E * E = (A * B) * (A * B) := by rw [hAB]
      _ = A * (B * A) * B := by simp only [Matrix.mul_assoc]
      _ = A * (1 : Matrix κ κ R) * B := by rw [hBA]
      _ = E := by rw [Matrix.mul_one, hAB]
  have hEA : E * A = A := by
    calc
      E * A = (A * B) * A := by rw [hAB]
      _ = A * (B * A) := by rw [Matrix.mul_assoc]
      _ = A := by rw [hBA, Matrix.mul_one]
  let P := LinearMap.range E.mulVecLin
  let f : P →ₗ[R] (κ → R) := B.mulVecLin.comp (LinearMap.range E.mulVecLin).subtype
  let g : (κ → R) →ₗ[R] P := A.mulVecLin.codRestrict P fun x ↦ by
    refine ⟨A.mulVecLin x, ?_⟩
    change (E.mulVecLin.comp A.mulVecLin) x = A.mulVecLin x
    rw [← Matrix.mulVecLin_mul, hEA]
  have hfg : f.comp g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change B.mulVecLin (A.mulVecLin x) = x
    change (B.mulVecLin.comp A.mulVecLin) x = x
    rw [← Matrix.mulVecLin_mul, hBA, Matrix.mulVecLin_one, LinearMap.id_apply]
  have hgf : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change A.mulVecLin (B.mulVecLin x) = x
    change (A.mulVecLin.comp B.mulVecLin) x = x
    rw [← Matrix.mulVecLin_mul, hAB]
    exact qs_mulVec_eq_self_of_mem_range hE x.property
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap f g hfg hgf).symm

theorem qs_exists_idempotent_range_equiv
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (E : Matrix (Fin n) (Fin n) R),
      E * E = E ∧ Nonempty (M ≃ₗ[R] LinearMap.range E.mulVecLin) := by
  classical
  obtain ⟨n, f, g, hf, _, hfg⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective R M
  let p : (Fin n → R) →ₗ[R] (Fin n → R) := g.comp f
  have hp : p.comp p = p := by
    apply LinearMap.ext
    intro x
    change g (f (g (f x))) = g (f x)
    have hx := LinearMap.congr_fun hfg (f x)
    change f (g (f x)) = f x at hx
    rw [hx]
  let E : Matrix (Fin n) (Fin n) R := LinearMap.toMatrix' p
  have hE : E * E = E := by
    calc
      E * E = LinearMap.toMatrix' (p.comp p) :=
        (LinearMap.toMatrix'_comp p p).symm
      _ = E := congrArg LinearMap.toMatrix' hp
  have hEp : E.mulVecLin = p := Matrix.toLin'_toMatrix' p
  let i : M →ₗ[R] LinearMap.range p := g.codRestrict (LinearMap.range p) fun m ↦ by
    obtain ⟨x, rfl⟩ := hf m
    exact ⟨x, rfl⟩
  let s : LinearMap.range p →ₗ[R] M := f.comp (LinearMap.range p).subtype
  have hsi : s.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun hfg x
  have his : i.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change p x = x
    rw [← hy]
    exact LinearMap.congr_fun hp y
  refine ⟨n, E, hE, ?_⟩
  rw [hEp]
  exact ⟨LinearEquiv.ofLinearMap i s his hsi⟩

theorem qs_free_of_matrix_equiv_one
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    {E : Matrix ι ι R}
    (e : M ≃ₗ[R] LinearMap.range E.mulVecLin)
    (h : qsMatrixEquiv E (1 : Matrix κ κ R)) : Module.Free R M := by
  let : Module.Free R (LinearMap.range E.mulVecLin) :=
    qs_free_range_of_equiv_one h
  exact Module.Free.of_equiv e.symm

theorem qs_zero_variables
    {k : Type*} [Field k]
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin 0) k) M] :
    Module.Free (MvPolynomial (Fin 0) k) M := by
  let e : MvPolynomial (Fin 0) k ≃+* k :=
    (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv
  let : Module k M := Module.compHom M e.symm.toRingHom
  exact Module.Free.of_basis <|
    (Module.Basis.ofVectorSpace k M).mapCoeffs e.symm fun _ _ ↦ rfl

theorem qs_idempotent_free
    (n : ℕ) (k : Type*) [Field k]
    {ι : Type*} [Fintype ι]
    (E : Matrix ι ι (MvPolynomial (Fin n) k)) (hE : E * E = E) :
    ∃ m : ℕ, qsMatrixEquiv E
      (1 : Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) k)) := by
  induction n generalizing k ι with
  | zero =>
      let P := LinearMap.range E.mulVecLin
      let _ : Module.Projective (MvPolynomial (Fin 0) k) P :=
        qs_range_projective E hE
      let _ : Module.Finite (MvPolynomial (Fin 0) k) P :=
        qs_range_finite E
      let _ : Module.Free (MvPolynomial (Fin 0) k) P :=
        qs_zero_variables
      exact qs_equiv_one_fin_of_free_range E hE
  | succ n ih =>
      let B := MvPolynomial (Fin n) k
      let e := MvPolynomial.finSuccEquiv k n
      let er : MvPolynomial (Fin (n + 1)) k →+* Polynomial B :=
        e.toRingEquiv.toRingHom
      let Ep := E.map er
      have hEp : Ep * Ep = Ep := qs_idempotent_map hE er
      let K := FractionRing (Polynomial k)
      let gen := qsGenericMap k n
      let Eg := Ep.map gen
      have hEg : Eg * Eg = Eg := qs_idempotent_map hEp gen
      obtain ⟨m, hm⟩ := ih K Eg hEg
      have hlocal : ∀ (p : Ideal B) (hp : p.IsMaximal),
          let _ : p.IsPrime := hp.isPrime
          ∃ r : ℕ, qsMatrixEquiv
            (Ep.map (Polynomial.mapRingHom
              (algebraMap B (Localization.AtPrime p))))
            (1 : Matrix (Fin r) (Fin r)
              (Polynomial (Localization.AtPrime p))) := by
        intro p hp
        let _ : p.IsPrime := hp.isPrime
        let A := Localization.AtPrime p
        let f : B →+* A := algebraMap B A
        let Q := Localization (qsMonicSubmonoid A)
        let alg : Polynomial A →+* Q := algebraMap (Polynomial A) Q
        let spec := qsGenericSpecialization k n A f
        have hcomp := qs_genericSpecialization_comp_genericMap k n A f
        have hmQ := hm.map spec
        rw [Matrix.map_one spec spec.map_zero spec.map_one] at hmQ
        have hmatrix : (Ep.map gen).map spec =
            Ep.map (alg.comp (Polynomial.mapRingHom f)) := by
          apply Matrix.ext
          intro i j
          exact DFunLike.congr_fun hcomp (Ep i j)
        rw [hmatrix] at hmQ
        have hmQ' : qsMatrixEquiv
            (Ep.map (alg.comp (Polynomial.mapRingHom f)))
            (1 : Matrix (Fin m) (Fin m) Q) := hmQ
        let Eloc := Ep.map (Polynomial.mapRingHom f)
        have hEloc : Eloc * Eloc = Eloc := by
          have h := congrArg
            (fun M ↦ M.map (Polynomial.mapRingHom f)) hEp
          simpa only [Eloc, Matrix.map_mul] using h
        have hmQloc : qsMatrixEquiv (Eloc.map alg)
            (1 : Matrix (Fin m) (Fin m) Q) := by
          have heq : Eloc.map alg =
              Ep.map (alg.comp (Polynomial.mapRingHom f)) := by
            apply Matrix.ext
            intro i j
            rfl
          rw [heq]
          exact hmQ'
        exact ⟨m, qs_horrocks_local A Eloc hEloc hmQloc⟩
      have hpatch := qs_quillen_patching Ep hEp hlocal
      let E₀ := Ep.map Polynomial.constantCoeff
      have hE₀ : E₀ * E₀ = E₀ :=
        qs_idempotent_map hEp Polynomial.constantCoeff
      obtain ⟨r, hr⟩ := ih k E₀ hE₀
      have hrpoly := hr.map (Polynomial.C : B →+* Polynomial B)
      rw [Matrix.map_one (Polynomial.C : B →+* Polynomial B)
        (map_zero _) (map_one _)] at hrpoly
      have hconstant : qsMatrixEquiv
          (Ep.map (qsConstantAtZero : Polynomial B →+* Polynomial B))
          (1 : Matrix (Fin r) (Fin r) (Polynomial B)) := by
        have heq : E₀.map (Polynomial.C : B →+* Polynomial B) =
            Ep.map (qsConstantAtZero : Polynomial B →+* Polynomial B) := by
          apply Matrix.ext
          intro i j
          rfl
        rw [← heq]
        exact hrpoly
      have hEpone : qsMatrixEquiv Ep
          (1 : Matrix (Fin r) (Fin r) (Polynomial B)) :=
        hpatch.trans hconstant hEp (by simp)
      have hback := hEpone.map e.symm.toRingEquiv.toRingHom
      rw [Matrix.map_one e.symm.toRingEquiv.toRingHom
        (map_zero _) (map_one _)] at hback
      have heq : Ep.map e.symm.toRingEquiv.toRingHom = E := by
        apply Matrix.ext
        intro i j
        exact e.symm_apply_apply (E i j)
      rw [heq] at hback
      exact ⟨r, hback⟩

/--
If `k` is a field and `M` is a finitely generated projective module over `MvPolynomial (Fin n) k`,
then `M` is free. Source: Serre's conjecture proved by D. Quillen, Invent. Math. 36 (1976) and A.
A. Suslin, Dokl. Akad. Nauk SSSR 229 (1976); Lam, Serre's Problem; Lean states field case over
`MvPolynomial (Fin n) k` with PID generalization existing.

Proves `Wanted` entry `quillen_suslin`.

Proof: The argument follows Quillen's induction and patching route, using Roberts'
idempotent-matrix proof of local Horrocks; see Quillen (1976), Lam, Lang, and Dicks.
-/
theorem quillen_suslin
    {k : Type*} [Field k]
    {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module.Finite (MvPolynomial (Fin n) k) M]
    [Module.Projective (MvPolynomial (Fin n) k) M] :
    Module.Free (MvPolynomial (Fin n) k) M := by
  obtain ⟨r, E, hE, ⟨e⟩⟩ :=
    qs_exists_idempotent_range_equiv
      (R := MvPolynomial (Fin n) k) (M := M)
  obtain ⟨m, hm⟩ := qs_idempotent_free n k E hE
  exact qs_free_of_matrix_equiv_one e hm

end QuillenSuslin
