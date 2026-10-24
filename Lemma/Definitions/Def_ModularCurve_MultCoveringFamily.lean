import Lemma.Definitions.Def_ModularCurve_MultCoveringCharts

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve.MultCovering

namespace ModularCurve.MultCovering

structure FamData (p : ℕ) [Fact p.Prime] (r : ℕ) where

  t : Fin r → ↥(modularFunctionFieldBar (1 * p))

  tRat : Fin r → ↥(modularFunctionFieldFull (1 * p))
  t_eq : ∀ l, t l = ⟨coeffEmb (AlgebraicClosure ℚ) ↑(tRat l),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (tRat l).2⟩

noncomputable def zeroSeries {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) : LaurentSeries ℚ :=
  ((frickeInvolutionFull (1 * p) (Φ.tRat l) : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ)

theorem coe_frickeInvolutionBar_t {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) :
    ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (zeroSeries Φ l) := by
  rw [Φ.t_eq l, frickeInvolutionBar_def, coe_geomAut_coeffEmb]
  rfl

open Classical in

noncomputable def hasseContent {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) : ℤ :=
  if h : ∃ n : ℤ, (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
      (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n)
  then h.choose else 0

noncomputable def hasseExp {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) : ℕ :=
  (hasseContent Φ l).toNat

noncomputable def goodFamilyZero {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamData p r) (l : Fin r) :
    modularFunctionFieldBar (1 * p) :=
  (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
      ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ * Φ.t l

section PerA
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

def ssPolyBar : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  ∏ e : Fin (mAnnuli p), (jBar (IsLocalRing.ResidueField ↥A)
    - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e))

def ssPolyBarZero : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  ∏ e : Fin (mAnnuli p), (jBar (IsLocalRing.ResidueField ↥A)
    - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e ^ p))

end PerA

structure FamCtx (p : ℕ) [Fact p.Prime] (r : ℕ) extends FamData p r where

  t_basis : IsEmbBasis (1 * p) t

  t_zero : ∀ l : Fin r, (l : ℕ) = 0 → t l = 1

  t_inf : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      ∃ hint : ∀ l, t l ∈ (infChart Γ).integers,
        (∀ l : Fin r, (l : ℕ) = 0 → (infChart Γ).residue ⟨t l, hint l⟩ = 1) ∧
        ∃ P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A),
          (∀ l : Fin r, 1 ≤ (l : ℕ) →
            (P l).natDegree + 1 ≤ mAnnuli p ∧
            (infChart Γ).residue ⟨t l, hint l⟩
              = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) ∧
          LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l) ∧
          Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range fun l : {l : Fin r // 1 ≤ (l : ℕ)} => P l)
            = Polynomial.degreeLT (IsLocalRing.ResidueField ↥A) (mAnnuli p)

  t_zeroChart : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (_ : A.LiesOverPrime p)
      [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A),
      (∀ e, ssValue Γ e ≠ 0 ∧ ssValue Γ e ≠ 1728) →
      ∃ (hint : ∀ l, goodFamilyZero toFamData l ∈ (zeroChart Γ).integers)
        (P : Fin r → Polynomial (IsLocalRing.ResidueField ↥A)),
        (∀ l, (P l).natDegree ≤ mAnnuli p) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) P ∧
        (∀ Q : Polynomial (IsLocalRing.ResidueField ↥A), Q.natDegree ≤ mAnnuli p →
          Q ∈ Submodule.span (IsLocalRing.ResidueField ↥A) (Set.range P)) ∧
        (∀ l : Fin r, (l : ℕ) = 0 →
          P l = ∏ e : Fin (mAnnuli p), (Polynomial.X - Polynomial.C (ssValue Γ e ^ p))) ∧
        ∀ l, (zeroChart Γ).residue ⟨goodFamilyZero toFamData l, hint l⟩ * ssPolyBarZero Γ
          = Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)

abbrev goodFamily {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r) : Fin r → ↥(modularFunctionFieldBar (1 * p)) :=
  Φ.t

end ModularCurve.MultCovering

end
