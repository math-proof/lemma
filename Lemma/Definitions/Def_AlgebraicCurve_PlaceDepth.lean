import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0
import Lemma.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

namespace Place

variable {L F : Type*} [Field L] [Field F] [Algebra L F]
variable (A : ValuationSubring L) (V : Place L F)

def HasValuation (f : F) (γ : A.ValueGroup) : Prop :=
  ∃ a : L, V.HasValue f a ∧ A.valuation a = γ

theorem hasValuation_iff (f : F) (γ : A.ValueGroup) :
    V.HasValuation A f γ ↔ ∃ a : L, V.HasValue f a ∧ A.valuation a = γ :=
  Iff.rfl

def HasDepth (f : F) (ϖ : L) (n : ℕ) : Prop :=
  V.HasValuation A f (A.valuation ϖ ^ n)

theorem hasDepth_iff (f : F) (ϖ : L) (n : ℕ) :
    V.HasDepth A f ϖ n ↔ ∃ a : L, V.HasValue f a ∧ A.valuation a = A.valuation ϖ ^ n :=
  Iff.rfl

def DepthBetween (f : F) (ϖ : L) (m n : ℕ) : Prop :=
  ∃ a : L, V.HasValue f a ∧ A.valuation ϖ ^ n < A.valuation a ∧ A.valuation a < A.valuation ϖ ^ m

theorem depthBetween_iff (f : F) (ϖ : L) (m n : ℕ) :
    V.DepthBetween A f ϖ m n ↔
      ∃ a : L, V.HasValue f a ∧ A.valuation ϖ ^ n < A.valuation a ∧ A.valuation a < A.valuation ϖ ^ m :=
  Iff.rfl

variable {A V}

theorem HasDepth.hasValuation {f : F} {ϖ : L} {n : ℕ} (h : V.HasDepth A f ϖ n) :
    V.HasValuation A f (A.valuation ϖ ^ n) :=
  h

theorem HasValuation.mul {f g : F} {γ δ : A.ValueGroup} (hf : V.HasValuation A f γ) (hg : V.HasValuation A g δ) :
    V.HasValuation A (f * g) (γ * δ) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  exact ⟨a * b, ha.mul hb, map_mul _ a b⟩

theorem HasDepth.mul {f g : F} {ϖ : L} {m n : ℕ} (hf : V.HasDepth A f ϖ m) (hg : V.HasDepth A g ϖ n) :
    V.HasDepth A (f * g) ϖ (m + n) := by
  have h := HasValuation.mul hf hg
  rwa [← pow_add] at h

theorem HasDepth.pow {f : F} {ϖ : L} {n : ℕ} (hf : V.HasDepth A f ϖ n) (d : ℕ) :
    V.HasDepth A (f ^ d) ϖ (d * n) := by
  induction d with
  | zero =>
    refine ⟨1, ?_, ?_⟩
    · rw [pow_zero]; exact hasValue_one V
    · rw [map_one, zero_mul, pow_zero]
  | succ d ih =>
    have h := HasDepth.mul ih hf
    rwa [← pow_succ, ← Nat.succ_mul] at h

variable (A V)

theorem hasValuation_algebraMap (c : L) : V.HasValuation A (algebraMap L F c) (A.valuation c) :=
  ⟨c, hasValue_algebraMap V c, rfl⟩

theorem hasDepth_algebraMap_pow (ϖ : L) (n : ℕ) : V.HasDepth A (algebraMap L F (ϖ ^ n)) ϖ n :=
  ⟨ϖ ^ n, hasValue_algebraMap V (ϖ ^ n), map_pow _ ϖ n⟩

theorem hasDepth_one_zero (ϖ : L) : V.HasDepth A (1 : F) ϖ 0 :=
  ⟨1, hasValue_one V, by rw [map_one, pow_zero]⟩

variable {A V}

theorem HasValuation.smul (g : SemilinearAut L F)
    (hg : ∀ a : L, A.valuation (SemilinearAut.baseAut g a) = A.valuation a)
    {f : F} {γ : A.ValueGroup} (h : V.HasValuation A f γ) :
    (g • V).HasValuation A (g • f) γ := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨SemilinearAut.baseAut g a, ha.smul g, hg a⟩

theorem HasDepth.smul (g : SemilinearAut L F)
    (hg : ∀ a : L, A.valuation (SemilinearAut.baseAut g a) = A.valuation a)
    {f : F} {ϖ : L} {n : ℕ} (h : V.HasDepth A f ϖ n) :
    (g • V).HasDepth A (g • f) ϖ n :=
  HasValuation.smul g hg h

theorem DepthBetween.smul (g : SemilinearAut L F)
    (hg : ∀ a : L, A.valuation (SemilinearAut.baseAut g a) = A.valuation a)
    {f : F} {ϖ : L} {m n : ℕ} (h : V.DepthBetween A f ϖ m n) :
    (g • V).DepthBetween A (g • f) ϖ m n := by
  obtain ⟨a, ha, h₁, h₂⟩ := h
  refine ⟨SemilinearAut.baseAut g a, ha.smul g, ?_, ?_⟩
  · rw [hg a]; exact h₁
  · rw [hg a]; exact h₂

variable (A V)

theorem HasValuation.eq_valuation_evalAt {f : F} {γ : A.ValueGroup} (hV : V.IsRational) (h : V.HasValuation A f γ) :
    γ = A.valuation (V.evalAt f) := by
  obtain ⟨a, ha, rfl⟩ := h
  have hres := V.algebraMap_evalAt hV ha.mem
  rw [ha.residue_eq] at hres
  rw [V.algebraMap_residueField_injective hres]

theorem hasValuation_iff_valuation_evalAt (hV : V.IsRational) (f : F) (γ : A.ValueGroup) :
    V.HasValuation A f γ ↔ ∃ h : f ∈ V.toValuationSubring, A.valuation (V.evalAt f) = γ := by
  constructor
  · rintro ⟨a, ha, hγ⟩
    have hres := V.algebraMap_evalAt hV ha.mem
    rw [ha.residue_eq] at hres
    have hfa : V.evalAt f = a := V.algebraMap_residueField_injective hres
    exact ⟨ha.mem, by rw [hfa]; exact hγ⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨V.evalAt f, ⟨hf, (V.algebraMap_evalAt hV hf).symm⟩, rfl⟩

theorem hasDepth_iff_valuation_evalAt (hV : V.IsRational) (f : F) (ϖ : L) (n : ℕ) :
    V.HasDepth A f ϖ n ↔ ∃ h : f ∈ V.toValuationSubring, A.valuation (V.evalAt f) = A.valuation ϖ ^ n :=
  hasValuation_iff_valuation_evalAt A V hV f _

end Place

end AlgebraicCurve

namespace ValuationSubring

variable {L F : Type*} [Field L] [Field F] [Algebra L F]

def IsAtDepth (O : ValuationSubring F) (f : F) (ϖ : L) (n : ℕ) : Prop :=
  O.valuation f = O.valuation (algebraMap L F ϖ) ^ n

theorem isAtDepth_iff (O : ValuationSubring F) (f : F) (ϖ : L) (n : ℕ) :
    O.IsAtDepth f ϖ n ↔ O.valuation f = O.valuation (algebraMap L F ϖ) ^ n :=
  Iff.rfl

variable {O : ValuationSubring F}

theorem IsAtDepth.mul {f g : F} {ϖ : L} {m n : ℕ} (hf : O.IsAtDepth f ϖ m) (hg : O.IsAtDepth g ϖ n) :
    O.IsAtDepth (f * g) ϖ (m + n) := by
  unfold IsAtDepth at hf hg ⊢
  rw [map_mul, hf, hg, pow_add]

variable (O) in

theorem isAtDepth_algebraMap_pow (ϖ : L) (n : ℕ) : O.IsAtDepth (algebraMap L F (ϖ ^ n)) ϖ n := by
  unfold IsAtDepth
  rw [map_pow, map_pow]

theorem isAtDepth_zero_of_isUnit {f : O} (hf : IsUnit f) (ϖ : L) : O.IsAtDepth (f : F) ϖ 0 := by
  unfold IsAtDepth
  rw [pow_zero]
  exact (O.valuation_eq_one_iff f).mp hf

end ValuationSubring

end
