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
import Def.Algebra.Module.QuillenSuslin.Part9
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qs_quotient_finite_of_monic_smul_mem
    (R : Type*) [CommRing R] [Nontrivial R]
    {κ : Type*} [Finite κ]
    (N : Submodule R (Matrix κ κ (Polynomial R)))
    (h : Polynomial R) (hh : h.Monic)
    (hN : ∀ G : Matrix κ κ (Polynomial R), h • G ∈ N) :
    Module.Finite R (Matrix κ κ (Polynomial R) ⧸ N) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let rem := qsMatrixRemainder R (ι := κ) (κ := κ) h hh
  let inc : Matrix κ κ (Polynomial.degreeLT R h.natDegree) →ₗ[R]
      Matrix κ κ (Polynomial R) :=
    LinearMap.mapMatrix (Polynomial.degreeLT R h.natDegree).subtype
  let f := N.mkQ.comp inc
  apply Module.Finite.of_surjective f
  intro z
  obtain ⟨G, rfl⟩ := N.mkQ_surjective z
  let D : Matrix κ κ (Polynomial R) := fun i j ↦ G i j /ₘ h
  refine ⟨rem G, ?_⟩
  change N.mkQ (inc (rem G)) = N.mkQ G
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  change inc (rem G) - G ∈ N
  have hdecomp : inc (rem G) + h • D = G := by
    apply Matrix.ext
    intro i j
    exact Polynomial.modByMonic_add_div (G i j) h
  have hdiff : inc (rem G) - G = -(h • D) := by
    calc
      inc (rem G) - G =
          inc (rem G) - (inc (rem G) + h • D) :=
        congrArg (fun X ↦ inc (rem G) - X) hdecomp.symm
      _ = -(h • D) := by abel
  rw [hdiff]
  exact N.neg_mem (hN D)

theorem qs_horrocks_range_sup_maximal_eq_top
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
    (hBA : B * A = 1)
    (hA : ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
      A.map (qsResidueMonicMap R) =
        C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))))
    (hB : ∃ D : Matrix κ ι (Polynomial (IsLocalRing.ResidueField R)),
      B.map (qsResidueMonicMap R) =
        D.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
    LinearMap.range (qsHorrocksMap R A) ⊔
        IsLocalRing.maximalIdeal R •
          (⊤ : Submodule R (Matrix κ κ (Polynomial R))) = ⊤ := by
  classical
  let k := IsLocalRing.ResidueField R
  let Q := Localization (qsMonicSubmonoid R)
  let K := Localization (qsMonicSubmonoid k)
  let alg : Polynomial R →+* Q := algebraMap (Polynomial R) Q
  let ak : Polynomial k →+* K := algebraMap (Polynomial k) K
  let q : Q →+* K := qsResidueMonicMap R
  let bar : Polynomial R →+* Polynomial k :=
    Polynomial.mapRingHom (IsLocalRing.residue R)
  obtain ⟨C, hAC⟩ := hA
  obtain ⟨D, hBD⟩ := hB
  have hDC : D.map ak * C.map ak = 1 := by
    calc
      D.map ak * C.map ak = B.map q * A.map q := by rw [hAC, hBD]
      _ = (B * A).map q := (Matrix.map_mul ..).symm
      _ = (1 : Matrix κ κ Q).map q := by rw [hBA]
      _ = 1 := Matrix.map_one q q.map_zero q.map_one
  apply top_unique
  intro G _
  have hGcompat : (G.map alg).map q = (G.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (G i j)
  have hGB : (G.map alg * B).map q = (G.map bar * D).map ak := by
    calc
      (G.map alg * B).map q = (G.map alg).map q * B.map q := Matrix.map_mul ..
      _ = (G.map bar).map ak * D.map ak := by rw [hGcompat, hBD]
      _ = (G.map bar * D).map ak := (Matrix.map_mul ..).symm
  let F := qsMatrixPolynomialPart R (G.map alg * B)
  have hFbar : F.map bar = G.map bar * D :=
    qsMatrixPolynomialPart_map_residue R (G.map alg * B) (G.map bar * D) hGB
  have hFcompat : (F.map alg).map q = (F.map bar).map ak := by
    apply Matrix.ext
    intro i j
    exact qsResidueMonicMap_algebraMap R (F i j)
  have hFA : (F.map alg * A).map q = (G.map bar).map ak := by
    calc
      (F.map alg * A).map q = (F.map alg).map q * A.map q := Matrix.map_mul ..
      _ = (F.map bar).map ak * C.map ak := by rw [hFcompat, hAC]
      _ = (G.map bar * D).map ak * C.map ak := by rw [hFbar]
      _ = (G.map bar).map ak * (D.map ak * C.map ak) := by
        rw [Matrix.map_mul, Matrix.mul_assoc]
      _ = (G.map bar).map ak := by rw [hDC, Matrix.mul_one]
  have hTbar : (qsHorrocksMap R A F).map bar = G.map bar := by
    rw [qsHorrocksMap_apply]
    exact qsMatrixPolynomialPart_map_residue R
      (F.map alg * A) (G.map bar) hFA
  have hdiff : G - qsHorrocksMap R A F ∈
      IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R (Matrix κ κ (Polynomial R))) := by
    apply qs_matrix_mem_maximal_smul_of_map_eq_zero R
    rw [Matrix.map_sub bar (map_sub bar), hTbar, sub_self]
  have hrange : qsHorrocksMap R A F ∈
      LinearMap.range (qsHorrocksMap R A) := ⟨F, rfl⟩
  have hsum : qsHorrocksMap R A F +
      (G - qsHorrocksMap R A F) = G := by abel
  rw [← hsum]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hrange)
    (Submodule.mem_sup_right hdiff)

theorem qs_horrocks_map_surjective
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι κ : Type*} [Fintype ι] [Finite κ] [DecidableEq κ]
    (A : Matrix ι κ (Localization (qsMonicSubmonoid R)))
    (B : Matrix κ ι (Localization (qsMonicSubmonoid R)))
    (hBA : B * A = 1)
    (hA : ∃ C : Matrix ι κ (Polynomial (IsLocalRing.ResidueField R)),
      A.map (qsResidueMonicMap R) =
        C.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))))
    (hB : ∃ D : Matrix κ ι (Polynomial (IsLocalRing.ResidueField R)),
      B.map (qsResidueMonicMap R) =
        D.map (algebraMap (Polynomial (IsLocalRing.ResidueField R))
          (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))) :
    Function.Surjective (qsHorrocksMap R A) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  let W := Matrix κ κ (Polynomial R)
  let T := qsHorrocksMap R A
  let N : Submodule R W := LinearMap.range T
  obtain ⟨h, hh, B₀, hB₀⟩ := qs_exists_monic_matrix_multiple R B
  have hmultiple : ∀ G : W, h • G ∈ N := fun G ↦
    qs_horrocks_multiple_mem_range R A B hBA h B₀ hB₀ G
  let _ : Module.Finite R (W ⧸ N) :=
    qs_quotient_finite_of_monic_smul_mem R N h hh hmultiple
  have hsup : N ⊔ IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R W) = ⊤ :=
    qs_horrocks_range_sup_maximal_eq_top R A B hBA hA hB
  have hmaptop : Submodule.map N.mkQ
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R W)) = ⊤ :=
    (Submodule.map_mkQ_eq_top N _).mpr hsup
  rw [Submodule.map_smul'', Submodule.map_top, N.range_mkQ] at hmaptop
  have hquot : (⊤ : Submodule R (W ⧸ N)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (IsLocalRing.maximalIdeal R) ⊤ Module.Finite.fg_top
      (by rw [hmaptop]) (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro G _
  have hz : N.mkQ G = 0 := by
    have : N.mkQ G ∈ (⊥ : Submodule R (W ⧸ N)) := by
      rw [← hquot]
      exact Submodule.mem_top
    exact this
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  exact hz

theorem qs_lift_invertible_matrix
    {A K : Type*} [CommRing A] [Field K]
    (f : A →+* K)
    (hlift : ∀ x : K, x ≠ 0 → ∃ u : Aˣ, f u = x)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hM : M.det ≠ 0) :
    ∃ U : Matrix ι ι A, IsUnit U.det ∧ U.map f = M := by
  classical
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun N ↦ ∃ U : Matrix ι ι A, IsUnit U.det ∧ U.map f = N) M hM
  · intro D hD
    have hDi : ∀ i, D i ≠ 0 := by
      intro i hi
      apply hD
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    choose u hu using fun i ↦ hlift (D i) (hDi i)
    refine ⟨Matrix.diagonal (fun i ↦ (u i : A)), ?_, ?_⟩
    · rw [Matrix.det_diagonal]
      exact IsUnit.prod_univ_iff.mpr fun i ↦ (u i).isUnit
    · ext i j
      by_cases hij : i = j
      · subst j
        simpa using hu i
      · simp [Matrix.diagonal, hij]
  · intro t
    obtain ⟨c, hc⟩ : ∃ c : A, f c = t.c := by
      by_cases hc0 : t.c = 0
      · exact ⟨0, by simp [hc0]⟩
      · obtain ⟨u, hu⟩ := hlift t.c hc0
        exact ⟨u, hu⟩
    refine ⟨Matrix.transvection t.i t.j c, ?_, ?_⟩
    · rw [Matrix.det_transvection_of_ne _ _ t.hij]
      exact isUnit_one
    · change (1 + Matrix.single t.i t.j c).map f =
        1 + Matrix.single t.i t.j t.c
      rw [Matrix.map_add f f.map_add, Matrix.map_one f f.map_zero f.map_one,
        Matrix.map_single t.i t.j c f, hc]
  · rintro X Y _hX _hY ⟨X', hXunit, hXmap⟩ ⟨Y', hYunit, hYmap⟩
    refine ⟨X' * Y', ?_, ?_⟩
    · rw [Matrix.det_mul]
      exact hXunit.mul hYunit
    · rw [Matrix.map_mul, hXmap, hYmap]

theorem qsResidueMonicMap_lifts_unit
    (R : Type*) [CommRing R] [IsLocalRing R]
    (z : Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R)))
    (hz : z ≠ 0) :
    ∃ u : (Localization (qsMonicSubmonoid R))ˣ,
      qsResidueMonicMap R u = z := by
  classical
  let k := IsLocalRing.ResidueField R
  let K := Localization (qsMonicSubmonoid k)
  let Q := Localization (qsMonicSubmonoid R)
  let _ : IsFractionRing (Polynomial k) K :=
    qs_monicLocalization_isFractionRing k
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (qsMonicSubmonoid k) z
  have hb0 : algebraMap (Polynomial k) K (b : Polynomial k) ≠ 0 := by
    intro hb
    exact b.property.ne_zero ((IsFractionRing.injective (Polynomial k) K) (by simpa using hb))
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, map_zero] at hab
    exact hz ((mul_eq_zero.mp hab).resolve_right hb0)
  let a' := a * Polynomial.C a.leadingCoeff⁻¹
  have ha'monic : a'.Monic := Polynomial.monic_mul_leadingCoeff_inv ha0
  obtain ⟨pa, hpamonic, hpamap⟩ :=
    qs_exists_monic_lift (IsLocalRing.residue R)
      IsLocalRing.residue_surjective ha'monic
  obtain ⟨pb, hpbmonic, hpbmap⟩ :=
    qs_exists_monic_lift (IsLocalRing.residue R)
      IsLocalRing.residue_surjective b.property
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective a.leadingCoeff
  have hlc0 : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
  have hrunit : IsUnit r :=
    (IsLocalRing.residue_ne_zero_iff_isUnit r).mp (by simpa [hr] using hlc0)
  have hscalar : IsUnit (algebraMap (Polynomial R) Q (Polynomial.C r)) :=
    (Polynomial.isUnit_C.mpr hrunit).map (algebraMap (Polynomial R) Q)
  have hpaunit : IsUnit (algebraMap (Polynomial R) Q pa) :=
    IsLocalization.map_units Q (⟨pa, hpamonic⟩ : qsMonicSubmonoid R)
  have hpbunit : IsUnit (algebraMap (Polynomial R) Q pb) :=
    IsLocalization.map_units Q (⟨pb, hpbmonic⟩ : qsMonicSubmonoid R)
  let u : Qˣ := hscalar.unit * hpaunit.unit * hpbunit.unit⁻¹
  refine ⟨u, ?_⟩
  have hscalarMap : qsResidueMonicMap R
      (algebraMap (Polynomial R) Q (Polynomial.C r)) =
      algebraMap (Polynomial k) K (Polynomial.C a.leadingCoeff) := by
    rw [qsResidueMonicMap_algebraMap, Polynomial.map_C, hr]
  have hpaMap : qsResidueMonicMap R
      (algebraMap (Polynomial R) Q pa) = algebraMap (Polynomial k) K a' := by
    rw [qsResidueMonicMap_algebraMap, hpamap]
  have hpbMap : qsResidueMonicMap R
      (algebraMap (Polynomial R) Q pb) =
      algebraMap (Polynomial k) K (b : Polynomial k) := by
    rw [qsResidueMonicMap_algebraMap, hpbmap]
  have hnormalize : Polynomial.C a.leadingCoeff * a' = a := by
    dsimp only [a']
    calc
      Polynomial.C a.leadingCoeff *
          (a * Polynomial.C a.leadingCoeff⁻¹) =
          a * (Polynomial.C a.leadingCoeff *
            Polynomial.C a.leadingCoeff⁻¹) := by ring
      _ = a := by rw [← Polynomial.C_mul, mul_inv_cancel₀ hlc0]; simp
  apply mul_right_cancel₀ hb0
  change qsResidueMonicMap R (↑u : Q) *
      algebraMap (Polynomial k) K (b : Polynomial k) =
    z * algebraMap (Polynomial k) K (b : Polynomial k)
  rw [hab]
  simp only [u, Units.val_mul, map_mul]
  rw [hscalar.unit_spec, hpaunit.unit_spec]
  rw [hscalarMap, hpaMap]
  have hnormalizeMap :
      algebraMap (Polynomial k) K (Polynomial.C a.leadingCoeff) *
        algebraMap (Polynomial k) K a' = algebraMap (Polynomial k) K a := by
    rw [← map_mul, hnormalize]
  rw [← hnormalizeMap]
  have hpbcoe : (↑hpbunit.unit : Q) = algebraMap (Polynomial R) Q pb :=
    hpbunit.unit_spec
  have hpbMap' : qsResidueMonicMap R (↑hpbunit.unit : Q) =
      algebraMap (Polynomial k) K (b : Polynomial k) := by
    rw [hpbcoe, hpbMap]
  rw [← hpbMap']
  have hcancel :
      qsResidueMonicMap R (↑(hpbunit.unit⁻¹) : Q) *
        qsResidueMonicMap R (↑hpbunit.unit : Q) = 1 := by
    rw [← map_mul]
    simp
  calc
    _ = algebraMap (Polynomial k) K (Polynomial.C a.leadingCoeff) *
        algebraMap (Polynomial k) K a' *
          (qsResidueMonicMap R (↑(hpbunit.unit⁻¹) : Q) *
            qsResidueMonicMap R (↑hpbunit.unit : Q)) := by ring
    _ = _ := by rw [hcancel, mul_one]

theorem qs_lift_residue_invertible_matrix
    (R : Type*) [CommRing R] [IsLocalRing R]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))))
    (hM : M.det ≠ 0) :
    ∃ U : Matrix ι ι (Localization (qsMonicSubmonoid R)),
      IsUnit U.det ∧ U.map (qsResidueMonicMap R) = M := by
  let _ : IsFractionRing (Polynomial (IsLocalRing.ResidueField R))
      (Localization (qsMonicSubmonoid (IsLocalRing.ResidueField R))) :=
    qs_monicLocalization_isFractionRing (IsLocalRing.ResidueField R)
  let _ : Field (Localization
      (qsMonicSubmonoid (IsLocalRing.ResidueField R))) :=
    IsFractionRing.toField (Polynomial (IsLocalRing.ResidueField R))
  exact qs_lift_invertible_matrix (qsResidueMonicMap R)
    (qsResidueMonicMap_lifts_unit R) M hM

theorem qsMatrixEquiv.refl
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i R} (hE : E * E = E) : qsMatrixEquiv E E :=
  ⟨E, E, hE, hE⟩

theorem qsShear_zero {R : Type*} [CommRing R] :
    qsShear (0 : R) =
      (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShear]
  · simp [qsShear]

theorem qsShiftX_comp_shear
    {R : Type*} [CommRing R] (j j' : R) :
    (qsShiftX j').comp (qsShear j) = qsShear (j + j') := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShiftX, qsShear]
  · simp [qsShiftX, qsShear]
    ring

theorem qsShiftX_comp_C
    {R : Type*} [CommRing R] (j : R) :
    (qsShiftX j).comp
        (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) =
      qsShear j := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsShiftX, qsShear]
  · simp [qsShiftX, qsShear]

theorem qsScaleY_comp_shear
    {R : Type*} [CommRing R] (r j : R) :
    (qsScaleY r).comp (qsShear j) = qsShear (r * j) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [qsScaleY, qsShear]
  · simp [qsScaleY, qsShear]
    ring

theorem qsScaleY_comp_C
    {R : Type*} [CommRing R] (r : R) :
    (qsScaleY r).comp
        (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) =
      (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [qsScaleY]
  · simp [qsScaleY]

theorem qs_scale_shear_map
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    (qsScaleY (f r)).comp
        ((qsShear (1 : S)).comp (Polynomial.mapRingHom f)) =
      (Polynomial.mapRingHom (Polynomial.mapRingHom f)).comp (qsShear r) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [qsScaleY, qsShear]
  · simp [qsScaleY, qsShear]

theorem qsEvalXY_comp_shear_one
    {R : Type*} [CommRing R] :
    (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
        (qsShear (1 : R)) = RingHom.id (Polynomial R) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsEvalXY, qsConstantAtZero, qsShear]
  · simp [qsEvalXY, qsConstantAtZero, qsShear]

theorem qsEvalXY_comp_C
    {R : Type*} [CommRing R] :
    (qsEvalXY : Polynomial (Polynomial R) →+* Polynomial R).comp
        Polynomial.C = qsConstantAtZero := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [qsEvalXY, qsConstantAtZero]
  · simp [qsEvalXY, qsConstantAtZero]

theorem qsMatrixEquiv.symm
    {R : Type*} [CommRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : Matrix ι ι R} {F : Matrix κ κ R}
    (h : qsMatrixEquiv E F) : qsMatrixEquiv F E := by
  obtain ⟨A, B, hAB, hBA⟩ := h
  exact ⟨B, A, hBA, hAB⟩

theorem qsMatrixEquiv.reindex_one
    {R : Type*} [CommRing R]
    {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    [DecidableEq κ] [DecidableEq η]
    {E : Matrix ι ι R}
    (h : qsMatrixEquiv E (1 : Matrix κ κ R)) (e : η ≃ κ) :
    qsMatrixEquiv E (1 : Matrix η η R) := by
  classical
  obtain ⟨A, B, hAB, hBA⟩ := h
  refine ⟨A.submatrix (Equiv.refl ι) e,
    B.submatrix e (Equiv.refl ι), ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv]
    simp [hAB]
  · rw [Matrix.submatrix_mul_equiv]
    rw [hBA]
    exact Matrix.submatrix_one_equiv e

theorem qsMatrixEquiv.map
    {R S : Type*} [CommRing R] [CommRing S]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {E : Matrix ι ι R} {F : Matrix κ κ R}
    (h : qsMatrixEquiv E F) (f : R →+* S) :
    qsMatrixEquiv (E.map f) (F.map f) := by
  obtain ⟨A, B, hAB, hBA⟩ := h
  refine ⟨A.map f, B.map f, ?_, ?_⟩
  · simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map f) hAB
  · simpa only [Matrix.map_mul] using congrArg (fun M ↦ M.map f) hBA

theorem qs_transition_one_of_equal_after
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {i k : Type*} [Fintype i] [Fintype k] [DecidableEq k]
    {E : Matrix i i R}
    (h : qsMatrixEquiv E (1 : Matrix k k R))
    (g₁ g₂ : R →+* S) (e : S →+* T)
    (he : e.comp g₁ = e.comp g₂) :
    ∃ C D : Matrix i i S,
      C * D = E.map g₁ ∧ D * C = E.map g₂ ∧
      C.map e = E.map (e.comp g₁) ∧
      D.map e = E.map (e.comp g₁) := by
  obtain ⟨A, B, hAB, hBA⟩ := h
  let C := A.map g₁ * B.map g₂
  let D := A.map g₂ * B.map g₁
  refine ⟨C, D, ?_, ?_, ?_, ?_⟩
  · calc
      C * D = A.map g₁ * (B.map g₂ * A.map g₂) * B.map g₁ := by
        simp only [C, D, Matrix.mul_assoc]
      _ = A.map g₁ * (B * A).map g₂ * B.map g₁ := by rw [Matrix.map_mul]
      _ = A.map g₁ * B.map g₁ := by rw [hBA]; simp
      _ = E.map g₁ := by rw [← Matrix.map_mul, hAB]
  · calc
      D * C = A.map g₂ * (B.map g₁ * A.map g₁) * B.map g₂ := by
        simp only [C, D, Matrix.mul_assoc]
      _ = A.map g₂ * (B * A).map g₁ * B.map g₂ := by rw [Matrix.map_mul]
      _ = A.map g₂ * B.map g₂ := by rw [hBA]; simp
      _ = E.map g₂ := by rw [← Matrix.map_mul, hAB]
  · simp only [C, Matrix.map_mul, Matrix.map_map]
    change
      (A.map ((e.comp g₁)) * B.map ((e.comp g₂))) = E.map (e.comp g₁)
    rw [← he, ← Matrix.map_mul, hAB]
  · simp only [D, Matrix.map_mul, Matrix.map_map]
    change
      (A.map ((e.comp g₂)) * B.map ((e.comp g₁))) = E.map (e.comp g₁)
    rw [← he, ← Matrix.map_mul, hAB]

theorem qsMatrixEquiv.trans
    {R : Type*} [CommRing R]
    {ι κ η : Type*} [Fintype ι] [Fintype κ] [Fintype η]
    {E : Matrix ι ι R} {F : Matrix κ κ R} {G : Matrix η η R}
    (hEF : qsMatrixEquiv E F) (hFG : qsMatrixEquiv F G)
    (hE : E * E = E) (hG : G * G = G) : qsMatrixEquiv E G := by
  obtain ⟨A, B, hAB, hBA⟩ := hEF
  obtain ⟨C, D, hCD, hDC⟩ := hFG
  refine ⟨A * C, D * B, ?_, ?_⟩
  · calc
      (A * C) * (D * B) = A * (C * D) * B := by simp only [Matrix.mul_assoc]
      _ = A * F * B := by rw [hCD]
      _ = A * (B * A) * B := by rw [hBA]
      _ = (A * B) * (A * B) := by simp only [Matrix.mul_assoc]
      _ = E * E := by rw [hAB]
      _ = E := hE
  · calc
      (D * B) * (A * C) = D * (B * A) * C := by simp only [Matrix.mul_assoc]
      _ = D * F * C := by rw [hBA]
      _ = D * (C * D) * C := by rw [hCD]
      _ = (D * C) * (D * C) := by simp only [Matrix.mul_assoc]
      _ = G * G := by rw [hDC]
      _ = G := hG

theorem qs_idempotent_map
    {R S : Type*} [CommRing R] [CommRing S]
    {i : Type*} [Fintype i]
    {E : Matrix i i R} (hE : E * E = E) (f : R →+* S) :
    E.map f * E.map f = E.map f := by
  rw [← Matrix.map_mul, hE]

theorem qs_patching_zero
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i (Polynomial R)} (hE : E * E = E) :
    qsMatrixEquiv (E.map (qsShear (0 : R)))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
  rw [qsShear_zero]
  exact qsMatrixEquiv.refl (qs_idempotent_map hE _)

theorem qs_patching_add
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i (Polynomial R)} (hE : E * E = E)
    {j j' : R}
    (hj : qsMatrixEquiv (E.map (qsShear j))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))))
    (hj' : qsMatrixEquiv (E.map (qsShear j'))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)))) :
    qsMatrixEquiv (E.map (qsShear (j + j')))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
  have hmap := hj.map (qsShiftX j')
  have hstep : qsMatrixEquiv (E.map (qsShear (j + j'))) (E.map (qsShear j')) := by
    change qsMatrixEquiv
      (E.map ((qsShiftX j').comp (qsShear j)))
      (E.map ((qsShiftX j').comp Polynomial.C)) at hmap
    rwa [qsShiftX_comp_shear, qsShiftX_comp_C] at hmap
  exact hstep.trans hj'
    (qs_idempotent_map hE _) (qs_idempotent_map hE _)

theorem qs_patching_mul
    {R : Type*} [CommRing R]
    {i : Type*} [Fintype i]
    {E : Matrix i i (Polynomial R)}
    {j : R}
    (hj : qsMatrixEquiv (E.map (qsShear j))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))))
    (r : R) :
    qsMatrixEquiv (E.map (qsShear (r * j)))
      (E.map (Polynomial.C : Polynomial R →+* Polynomial (Polynomial R))) := by
  have hmap := hj.map (qsScaleY r)
  change qsMatrixEquiv
    (E.map ((qsScaleY r).comp (qsShear j)))
    (E.map ((qsScaleY r).comp Polynomial.C)) at hmap
  rwa [qsScaleY_comp_shear, qsScaleY_comp_C] at hmap

end QuillenSuslin
