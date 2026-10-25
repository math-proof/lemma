import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.RegularProlongation
import Lemma.Int.P2MUtil

open AlgebraicCurve IsLocalRing Polynomial

/--
[AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean)
-/
@[path]
private lemma main
  [Field L] [Field F] [Algebra L F] [Field Fbar]
  {A : ValuationSubring L} [Algebra (IsLocalRing.ResidueField A) Fbar]
  {R : RegularProlongation A F Fbar}
  {x : R.integers}
  {c : Polynomial L}
  {i : ℕ}
-- given
  (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
  (hc : Polynomial.aeval (x : F) c ∈ R.integers) :
-- imply
  c.coeff i ∈ A := by
-- proof
  classical

  by_cases hci : c.coeff i = 0
  · exact hci ▸ A.zero_mem
  have hi : i ∈ c.support := Polynomial.mem_support_iff.mpr hci

  obtain ⟨j₀, hj₀, hj₀max⟩ := Finset.exists_max_image c.support
    (fun j => A.valuation (c.coeff j)) ⟨i, hi⟩
  have hcj₀ : c.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀

  suffices hAj₀ : c.coeff j₀ ∈ A by
    rw [← A.valuation_le_one_iff] at hAj₀ ⊢
    exact (hj₀max i hi).trans hAj₀
  by_contra hnA

  set s : L := (c.coeff j₀)⁻¹ with hs
  have hsnon : s ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hnA)
  have hsA : s ∈ A := (A.valuation_le_one_iff s).mp (A.mem_nonunits_iff.mp hsnon).le
  have hsres : IsLocalRing.residue A ⟨s, hsA⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (A.coe_mem_nonunits_iff.mp hsnon)

  have hcoeff : ∀ j, s * c.coeff j ∈ A := by
    intro j
    by_cases hj : j ∈ c.support
    · have hv := hj₀max j hj
      rw [← A.valuation_le_one_iff, map_mul, hs, map_inv₀]
      have hvj₀ : A.valuation (c.coeff j₀) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact hcj₀
      calc (A.valuation (c.coeff j₀))⁻¹ * A.valuation (c.coeff j)
          ≤ (A.valuation (c.coeff j₀))⁻¹ * A.valuation (c.coeff j₀) :=
            mul_le_mul_right hv _
        _ = 1 := inv_mul_cancel₀ hvj₀
    · rw [Polynomial.notMem_support_iff.mp hj, mul_zero]; exact A.zero_mem

  set c' : Polynomial A := c.support.sum
    (fun j => Polynomial.C ⟨s * c.coeff j, hcoeff j⟩ * Polynomial.X ^ j) with hc'
  have hc'map : c'.map A.subtype = s • c := by
    rw [hc']; ext j
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Polynomial.coeff_smul, smul_eq_mul]
    rw [Finset.sum_ite_eq c.support j]
    by_cases hj : j ∈ c.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]

  have hc'j₀ : c'.coeff j₀ = 1 := by
    rw [hc']
    simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq c.support j₀, if_pos hj₀]
    exact Subtype.ext (show s * c.coeff j₀ = 1 from by rw [hs, inv_mul_cancel₀ hcj₀])

  set cbar : Polynomial (ResidueField A) := c'.map (IsLocalRing.residue A) with hcbar
  have hcbar0 : cbar ≠ 0 := by
    intro h0
    have : cbar.coeff j₀ = 0 := by rw [h0]; simp
    rw [hcbar, Polynomial.coeff_map, hc'j₀, map_one] at this
    exact one_ne_zero this

  let φ : A →+* R.integers :=
    { toFun := fun a => ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hresφ : R.residue.comp φ = (algebraMap (ResidueField A) Fbar).comp (residue A) := by
    ext a; exact R.residue_algebraMap a

  have hresEval : R.residue (Polynomial.eval₂ φ x c') =
      Polynomial.aeval (R.residue x) cbar := by
    calc R.residue (Polynomial.eval₂ φ x c')
        = Polynomial.eval₂ (R.residue.comp φ) (R.residue x) c' :=
          Polynomial.hom_eval₂ c' φ R.residue x
      _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (residue A))
            (R.residue x) c' := by rw [hresφ]
      _ = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue x)
            (c'.map (residue A)) := by rw [Polynomial.eval₂_map]
      _ = Polynomial.aeval (R.residue x) cbar := by rw [hcbar, Polynomial.aeval_def]
  have hne0 : R.residue (Polynomial.eval₂ φ x c') ≠ 0 := by
    rw [hresEval]
    exact fun h => hx ⟨cbar, hcbar0, h⟩

  have hfactor : (Polynomial.eval₂ φ x c' : R.integers) = φ ⟨s, hsA⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((Polynomial.eval₂ φ x c' : R.integers) : F) =
      algebraMap L F s * Polynomial.aeval (x : F) c
    have h1 : ((Polynomial.eval₂ φ x c' : R.integers) : F) =
        Polynomial.eval₂ ((algebraMap L F).comp A.subtype) (↑x) c' := by
      have hsub : R.integers.subtype.comp φ = (algebraMap L F).comp A.subtype := by
        ext a; rfl
      rw [← hsub]
      exact Polynomial.hom_eval₂ c' φ R.integers.subtype x
    rw [h1, ← Polynomial.eval₂_map, ← Polynomial.aeval_def, hc'map, map_smul,
      Algebra.smul_def]
  apply hne0
  rw [hfactor, map_mul]
  have hresφs : R.residue (φ ⟨s, hsA⟩) = 0 := by
    change (R.residue.comp φ) ⟨s, hsA⟩ = 0
    rw [hresφ]
    change algebraMap (ResidueField A) Fbar (residue A ⟨s, hsA⟩) = 0
    rw [hsres, map_zero]
  rw [hresφs, zero_mul]


-- created on 2026-10-23
