import Lemma.Definitions.Def_AlgebraicCurve_SemistableCharts
import Lemma.Definitions.Def_AlgebraicCurve_ChordalProximity
import Lemma.Definitions.Def_ModularCurve_SupersingularModuli
import Lemma.Definitions.Def_ModularCurve_LevelOneProlongationPair
import Lemma.Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Lemma.Definitions.Def_ModularCurve_LevelOneChartFst

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicCurve IsLocalRing

namespace ModularCurve.MultCovering

section Instances
variable (A : ValuationSubring (AlgebraicClosure ℚ))

instance instFieldFbar : Field ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) := inferInstance

instance instAlgebraFbar :
    Algebra (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  inferInstance

end Instances

abbrev jF (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * p) (jq_mem (1 * p)))⟩

abbrev jpF (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (dvd_mul_left p 1))⟩

abbrev tieG (p : ℕ) [Fact p.Prime] : modularFunctionFieldBar (1 * p) := jpF p - jF p ^ p

theorem jF_eq_jFun (p : ℕ) [Fact p.Prime] : jF p = PlaceSpecialization.jFun (q := p) := rfl

abbrev jBar (k : Type) [Field k] : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩

abbrev nCharts : ℕ := 2

def mAnnuli (p : ℕ) : ℕ := p / 12 + (if p % 3 = 2 then 1 else 0) + (if p % 4 = 3 then 1 else 0)

def modulusExp : ℕ := 3

abbrev Fbar (A : ValuationSubring (AlgebraicClosure ℚ)) (_i : Fin nCharts) : Type :=
  ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)

abbrev IsSSCentred (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (a : IsLocalRing.ResidueField ↥A) : Prop :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.IsSSCentred A p W a

structure ChartCtx (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] where
  data  : ModularPolynomialData p
  hKr   : KroneckerCongruence p data
  hα    : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p
  hβ    : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p
  P     : PlaceSpecialization A p 1 data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ
  R     : P.LevelOneProlongationPair

  S₁    : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))

  Wn    : Finset (Place (IsLocalRing.ResidueField ↥A) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1))
  hWn   : ∀ w, w ∈ Wn ↔ w ∈ ssPlaces p 1 (IsLocalRing.ResidueField ↥A)

  hfin  : (ssJSet p (IsLocalRing.ResidueField ↥A)).Finite
  hcard : hfin.toFinset.card = mAnnuli p

  supply : R.ChartFstSupply S₁

section PerA

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

def infChart :
    ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply

def zeroChart :
    ComponentChart A ↥(modularFunctionFieldBar (1 * p)) ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1) :=
  (infChart Γ).comap (frickeInvolutionBar (1 * p))

def chart (i : Fin nCharts) : ComponentChart A ↥(modularFunctionFieldBar (1 * p)) (Fbar A i) :=
  ![infChart Γ, zeroChart Γ] i

@[simp] theorem chart_zero : chart Γ 0 = infChart Γ := rfl
@[simp] theorem chart_one : chart Γ 1 = zeroChart Γ := rfl

def src (p : ℕ) (_e : Fin (mAnnuli p)) : Fin nCharts := 1

def tgt (p : ℕ) (_e : Fin (mAnnuli p)) : Fin nCharts := 0

def ssValue (e : Fin (mAnnuli p)) : IsLocalRing.ResidueField ↥A :=
  ((Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm e : ↥Γ.hfin.toFinset)

theorem ssValue_mem_toFinset (e : Fin (mAnnuli p)) : ssValue Γ e ∈ Γ.hfin.toFinset :=
  ((Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm e).2

theorem ssValue_mem_ssJSet (e : Fin (mAnnuli p)) : ssValue Γ e ∈ ssJSet p (IsLocalRing.ResidueField ↥A) :=
  Γ.hfin.mem_toFinset.mp (ssValue_mem_toFinset Γ e)

theorem ssValue_injective : Function.Injective (ssValue Γ) := fun _ _ h =>
  (Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard).symm.injective (Subtype.ext h)

theorem exists_ssValue_eq (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ∃ e, ssValue Γ e = a :=
  ⟨Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard ⟨a, Γ.hfin.mem_toFinset.mpr ha⟩, by simp [ssValue]⟩

def edgeOf (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) : Fin (mAnnuli p) :=
  Γ.hfin.toFinset.equivFinOfCardEq Γ.hcard ⟨a, Γ.hfin.mem_toFinset.mpr ha⟩

@[simp] theorem ssValue_edgeOf (a : IsLocalRing.ResidueField ↥A) (ha : a ∈ ssJSet p (IsLocalRing.ResidueField ↥A)) :
    ssValue Γ (edgeOf Γ a ha) = a := by
  simp [ssValue, edgeOf]

def nodeSrc (e : Fin (mAnnuli p)) : Place (IsLocalRing.ResidueField ↥A) (Fbar A (src p e)) :=
  charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e ^ p)

def nodeTgt (e : Fin (mAnnuli p)) : Place (IsLocalRing.ResidueField ↥A) (Fbar A (tgt p e)) :=
  charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)

theorem nodeSrc_eq (e : Fin (mAnnuli p)) : nodeSrc Γ e = (frobNodePair p (ssValue Γ e)).2 := rfl
theorem nodeTgt_eq (e : Fin (mAnnuli p)) : nodeTgt Γ e = (frobNodePair p (ssValue Γ e)).1 := rfl

def ordBranch : Set (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) := Γ.S₁

end PerA

def Statement (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar lvl) : Prop :=
    ∃ (n m B k : ℕ) (Cc : ℝ), 0 < m ∧ ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar lvl) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar lvl)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar lvl),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar lvl ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full lvl (jq_mem lvl))⟩ : modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full lvl hpl)⟩ :
                modularFunctionFieldBar lvl)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar lvl) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)))

def StatementAll (p : ℕ) (hp : p.Prime) (lvl : ℕ) [NeZero lvl] (hpl : p ∣ lvl) : Prop :=
  ∀ {r : ℕ} (s : Fin r → modularFunctionFieldBar lvl), IsEmbBasis lvl s → Statement p hp lvl hpl s

theorem StatementAll_congr (p : ℕ) (hp : p.Prime) {l₁ l₂ : ℕ} [NeZero l₁] [NeZero l₂] (h : l₁ = l₂)
    (h₁ : p ∣ l₁) (h₂ : p ∣ l₂) : StatementAll p hp l₁ h₁ → StatementAll p hp l₂ h₂ := by
  subst h
  exact id

end ModularCurve.MultCovering

end
