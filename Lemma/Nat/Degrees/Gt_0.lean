import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.CSTTheorem.Part2


/--
[cst_pos_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma cst_pos_degrees
  {cst : CSTPartIIData}
  {cst : CSTPartIIData} :
-- imply
  ∀ i, 0 < cst.degrees i := by
-- proof
  intro i
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  have h0 := cst.basicInvariants_homogeneous i
  rw [h] at h0
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous] at h0
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
  set c := MvPolynomial.coeff 0 (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)
  have hxi : cst.basicInvariants i = algebraMap ℂ _ c := by
    ext; simp [h0, MvPolynomial.algebraMap_eq]
  have hp : MvPolynomial.aeval cst.basicInvariants
    (MvPolynomial.X i - MvPolynomial.C c) = (0 : ↥cst.invariantSubalgebra) := by
    simp [hxi]
  have hne : MvPolynomial.X i - MvPolynomial.C c ≠
    (0 : MvPolynomial (Fin cst.n) ℂ) := by
    intro h
    have h1 := sub_eq_zero.mp h
    have h2 := MvPolynomial.totalDegree_X (R := ℂ) i
    have h3 := MvPolynomial.totalDegree_C (σ := Fin cst.n) c
    linarith [congr_arg MvPolynomial.totalDegree h1]
  exact hne (cst.alg_independent hp)

/--
[cst_finite_over_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma cst_finite_over_invariants
  {cst : CSTPartIIData}
  {cst : CSTPartIIData} :
-- imply
  Module.Finite (Algebra.adjoin ℂ (Set.range (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)))) (MvPolynomial (Fin cst.n) ℂ) := by
-- proof
  set S := Algebra.adjoin ℂ (Set.range (fun i =>
    (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)))
  haveI : Algebra.FiniteType (↥S) (MvPolynomial (Fin cst.n) ℂ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  suffices Algebra.IsIntegral (↥S) (MvPolynomial (Fin cst.n) ℂ) from
    Algebra.IsIntegral.finite
  have hS_eq : S = cst.invariantSubalgebra := by
    apply le_antisymm
    ·
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact (cst.basicInvariants i).2
    ·
      intro p hp
      have hmem : (⟨p, hp⟩ : ↥cst.invariantSubalgebra) ∈
        Algebra.adjoin ℂ (Set.range cst.basicInvariants) :=
        cst.generators_generate ▸ Algebra.mem_top
      have key : ∀ (x : ↥cst.invariantSubalgebra),
        x ∈ Algebra.adjoin ℂ (Set.range cst.basicInvariants) →
        (x : MvPolynomial (Fin cst.n) ℂ) ∈ S := by
        intro x hx
        induction hx using Algebra.adjoin_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        | algebraMap r => exact S.algebraMap_mem r
        | add _ _ _ _ ha hb => exact S.add_mem ha hb
        | mul _ _ _ _ ha hb => exact S.mul_mem ha hb
      exact key ⟨p, hp⟩ hmem
  letI : MulSemiringAction cst.G (MvPolynomial (Fin cst.n) ℂ) :=
    MulSemiringAction.compHom _
      { toFun := fun g => (cst.algAct g).toRingEquiv
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
  have hsmul : ∀ (g : cst.G) (f : MvPolynomial (Fin cst.n) ℂ),
    g • f = cst.algAct g f := fun _ _ => rfl
  letI : SMulCommClass cst.G ℂ (MvPolynomial (Fin cst.n) ℂ) :=
    ⟨fun g c f => by
      show cst.algAct g (c • f) = c • (cst.algAct g f)
      rw [Algebra.smul_def, map_mul, (cst.algAct g).commutes, ← Algebra.smul_def]⟩
  haveI : Algebra.IsInvariant (↥S) (MvPolynomial (Fin cst.n) ℂ) cst.G := by
    constructor
    intro b hb
    have hb_inv : b ∈ cst.invariantSubalgebra := by
      rw [cst.mem_invariant_iff]; intro g; exact hsmul g b ▸ hb g
    have hb_S : b ∈ S := hS_eq ▸ hb_inv
    exact ⟨⟨b, hb_S⟩, rfl⟩
  exact Algebra.IsInvariant.isIntegral (↥S) (MvPolynomial (Fin cst.n) ℂ) cst.G

/--
[qIntegerCST_eq_qAnalog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma qIntegerCST_eq_qAnalog
  {cst : CSTPartIIData}
  {d : ℕ} :
-- imply
  qIntegerCST d = qAnalog d := by
-- proof
  simp only [qIntegerCST, qAnalog]
  ext n
  simp [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_X_pow]

/--
[quotientGradedComponent_eq_quotientHomogeneousSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma quotientGradedComponent_eq_quotientHomogeneousSubmodule
  {cst : CSTPartIIData}
  {n : ℕ}
  {I : Ideal (MvPolynomial (Fin n) ℂ)}
  {N : ℕ} :
-- imply
  quotientGradedComponent n I N = quotientHomogeneousSubmodule ℂ n I N :=
-- proof
  rfl

/--
[isHomogeneous_to_coeff_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma isHomogeneous_to_coeff_form
  {cst : CSTPartIIData}
  {n : ℕ}
  {p : MvPolynomial (Fin n) ℂ}
  {d : ℕ}
-- given
  (hp : p.IsHomogeneous d) :
-- imply
  ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m p ≠ 0 → (m.sum fun _ e => e) = d := by
-- proof
  intro m hm
  have := hp hm
  simp [Finsupp.weight_apply] at this
  exact this

/--
[cst_hilbert_series_helper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma cst_hilbert_series_helper
  {cst : CSTPartIIData}
  {cst : CSTPartIIData} :
-- imply
  ∀ N : ℕ, ↑(Module.finrank ℂ (quotientGradedComponent cst.n (Ideal.span (Set.range (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)))) N)) = (PowerSeries.coeff N) (∏ i : Fin cst.n, qIntegerCST (cst.degrees i)) := by
-- proof
  set f := (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)) with hf_def
  set I := Ideal.span (Set.range f) with hI_def
  have hhom : ∀ i, ∀ (m : Fin cst.n →₀ ℕ),
    MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = cst.degrees i :=
    fun i => isHomogeneous_to_coeff_form (cst.basicInvariants_homogeneous i)
  have hvanish : ∀ (v : Fin cst.n → ℂ),
    (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0 :=
    cst.basicInvariants_vanish
  have hHS := prop_12_10_hilbert_series ℂ cst.n inferInstance f cst.degrees
    (cst_pos_degrees cst) hhom hvanish (cst_finite_over_invariants cst)
  intro N
  have hcoeff : ∀ M : ℕ,
    (PowerSeries.coeff M) (hilbertSeries (quotientHomogeneousSubmodule ℂ cst.n I)) =
    (PowerSeries.coeff M) (∏ i : Fin cst.n, qAnalog (cst.degrees i)) :=
    fun M => by rw [hHS]
  specialize hcoeff N
  simp only [hilbertSeries, PowerSeries.coeff_mk] at hcoeff
  rw [quotientGradedComponent_eq_quotientHomogeneousSubmodule]
  rw [show ∏ i : Fin cst.n, qIntegerCST (cst.degrees i) =
    ∏ i : Fin cst.n, qAnalog (cst.degrees i) from
    Finset.prod_congr rfl (fun i _ => qIntegerCST_eq_qAnalog (cst.degrees i))]
  exact hcoeff

/--
[qIntPoly_coe_eq_qIntegerCST](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma qIntPoly_coe_eq_qIntegerCST
  {cst : CSTPartIIData}
  {d : ℕ} :
-- imply
  (qIntPoly d : PowerSeries ℤ) = qIntegerCST d := by
-- proof
  ext n; simp only [qIntPoly, qIntegerCST]
  simp [Polynomial.coeff_coe, Polynomial.coeff_X_pow, PowerSeries.coeff_X_pow, map_sum]

/--
[qIntPoly_eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma qIntPoly_eval_one
  {cst : CSTPartIIData}
  {d : ℕ} :
-- imply
  Polynomial.eval 1 (qIntPoly d) = ↑d := by
-- proof
  simp only [qIntPoly]; simp [Polynomial.eval_finset_sum, Polynomial.eval_pow]

/--
[prod_qIntPoly_coe_eq_prod_qIntegerCST](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma prod_qIntPoly_coe_eq_prod_qIntegerCST
  {cst : CSTPartIIData}
  {n : ℕ}
  {degrees : Fin n → ℕ} :
-- imply
  ((∏ i : Fin n, qIntPoly (degrees i) : Polynomial ℤ) : PowerSeries ℤ) = ∏ i : Fin n, qIntegerCST (degrees i) := by
-- proof
  rw [show (↑(∏ i : Fin n, qIntPoly (degrees i)) : PowerSeries ℤ) =
    Polynomial.coeToPowerSeries.ringHom (∏ i, qIntPoly (degrees i)) from rfl]
  rw [map_prod]; congr 1; funext i
  show (qIntPoly (degrees i) : PowerSeries ℤ) = _
  exact qIntPoly_coe_eq_qIntegerCST (degrees i)

/--
[prod_qIntCST_coeff_eq_poly_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma prod_qIntCST_coeff_eq_poly_coeff
  {cst : CSTPartIIData}
  {n : ℕ}
  {degrees : Fin n → ℕ}
  {N : ℕ} :
-- imply
  (PowerSeries.coeff N) (∏ i : Fin n, qIntegerCST (degrees i)) = (∏ i : Fin n, qIntPoly (degrees i)).coeff N := by
-- proof
  rw [← prod_qIntPoly_coe_eq_prod_qIntegerCST]; simp [Polynomial.coeff_coe]

/--
[sum_poly_coeff_eq_eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma sum_poly_coeff_eq_eval_one
  {cst : CSTPartIIData}
  {p : Polynomial ℤ}
  {B : ℕ}
-- given
  (hB : p.natDegree < B) :
-- imply
  ∑ i ∈ Finset.range B, p.coeff i = Polynomial.eval 1 p := by
-- proof
  rw [Polynomial.eval_eq_sum_range]; simp only [one_pow, mul_one]; symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro x hx1 hx2
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Finset.mem_range] at hx1 hx2; omega)

/--
[sum_prod_qIntCST_coeff_eq_prod_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CSTTheorem.lean)
-/
@[path]
private lemma sum_prod_qIntCST_coeff_eq_prod_degrees
  {cst : CSTPartIIData}
  {n : ℕ}
  {degrees : Fin n → ℕ}
  {B : ℕ}
-- given
  (hB : (∏ i : Fin n, qIntPoly (degrees i)).natDegree < B) :
-- imply
  ∑ N ∈ Finset.range B, (PowerSeries.coeff N) (∏ i : Fin n, qIntegerCST (degrees i)) = ↑(∏ i : Fin n, degrees i) := by
-- proof
  simp_rw [prod_qIntCST_coeff_eq_poly_coeff]
  rw [sum_poly_coeff_eq_eval_one hB]
  simp [Polynomial.eval_prod, qIntPoly_eval_one]
section CSTHomGradedProjective
set_option synthInstance.maxHeartbeats 200000
end CSTHomGradedProjective


-- created on 2026-10-24
