import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Topology.LocallyConstant.Basic

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace LanglandsTunnell.TateLocal

section Modulus

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]

def modulus (a : K) : ℝ≥0 := by
  classical exact if h : a = 0 then 0 else distribHaarChar K (Units.mk0 a h)

@[simp] theorem modulus_zero : modulus (0 : K) = 0 := by
  simp [modulus]

theorem modulus_of_ne_zero {a : K} (h : a ≠ 0) : modulus a = distribHaarChar K (Units.mk0 a h) := by
  simp [modulus, h]

@[simp] theorem modulus_coe_units (u : Kˣ) : modulus (u : K) = distribHaarChar K u := by
  rw [modulus_of_ne_zero u.ne_zero, Units.mk0_val]

theorem modulus_pos {a : K} (h : a ≠ 0) : 0 < modulus a := by
  rw [modulus_of_ne_zero h]
  exact distribHaarChar_pos

theorem modulus_ne_zero {a : K} (h : a ≠ 0) : modulus a ≠ 0 :=
  (modulus_pos h).ne'

@[simp] theorem modulus_one : modulus (1 : K) = 1 := by
  rw [modulus_of_ne_zero one_ne_zero, Units.mk0_one, map_one]

theorem modulus_mul (a b : K) : modulus (a * b) = modulus a * modulus b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [modulus_of_ne_zero (mul_ne_zero ha hb), modulus_of_ne_zero ha, modulus_of_ne_zero hb,
    ← map_mul]
  congr 1
  exact Units.ext rfl

end Modulus

section TestFunctions

variable {K : Type*} [TopologicalSpace K]

def IsSchwartzBruhat (f : K → ℂ) : Prop :=
  IsLocallyConstant f ∧ HasCompactSupport f

theorem IsSchwartzBruhat.zero : IsSchwartzBruhat (0 : K → ℂ) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem IsSchwartzBruhat.indicator_const {U : Set K} (hU : IsClopen U) (hUc : IsCompact U)
    (c : ℂ) : IsSchwartzBruhat (U.indicator fun _ => c) := by
  refine ⟨?_, ?_⟩
  · intro s
    classical
    have : (U.indicator fun _ => c) ⁻¹' s =
        (if c ∈ s then U else ∅) ∪ (if (0 : ℂ) ∈ s then Uᶜ else ∅) := by
      ext x
      by_cases hx : x ∈ U <;> by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
        simp [Set.indicator, hx, hc, h0]
    rw [this]
    refine IsOpen.union ?_ ?_
    · split_ifs
      · exact hU.isOpen
      · exact isOpen_empty
    · split_ifs
      · exact hU.compl.isOpen
      · exact isOpen_empty
  · exact HasCompactSupport.intro' hUc hU.isClosed fun x hx => Set.indicator_of_notMem hx _

end TestFunctions

section Fourier

variable {K : Type*} [Field K] [MeasurableSpace K]

def tateFourier (ψ : AddChar K ℂ) (μ : Measure K) (f : K → ℂ) (y : K) : ℂ :=
  ∫ x, f x * ψ (x * y) ∂μ

theorem tateFourier_zero_fun (ψ : AddChar K ℂ) (μ : Measure K) :
    tateFourier ψ μ (0 : K → ℂ) = 0 := by
  funext y
  simp [tateFourier]

end Fourier

section Characters

variable {K : Type*} [Field K]

def charExt (χ : Kˣ →* ℂˣ) (x : K) : ℂ := by
  classical exact if h : x = 0 then 0 else (χ (Units.mk0 x h) : ℂ)

@[simp] theorem charExt_zero (χ : Kˣ →* ℂˣ) : charExt χ (0 : K) = 0 := by
  simp [charExt]

theorem charExt_of_ne_zero (χ : Kˣ →* ℂˣ) {x : K} (h : x ≠ 0) :
    charExt χ x = χ (Units.mk0 x h) := by
  simp [charExt, h]

@[simp] theorem charExt_coe_units (χ : Kˣ →* ℂˣ) (u : Kˣ) : charExt χ (u : K) = χ u := by
  rw [charExt_of_ne_zero χ u.ne_zero, Units.mk0_val]

theorem charExt_one_of_ne_zero {x : K} (h : x ≠ 0) : charExt (1 : Kˣ →* ℂˣ) x = 1 := by
  rw [charExt_of_ne_zero _ h, MonoidHom.one_apply, Units.val_one]

end Characters

section Zeta

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K]

def mulMeasure (μ : Measure K) : Measure K :=
  (μ.restrict {0}ᶜ).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹

def localZeta (μ : Measure K) (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((modulus x : ℝ) : ℂ) ^ s ∂(mulMeasure μ)

theorem localZeta_zero_fun (μ : Measure K) (χ : Kˣ →* ℂˣ) (s : ℂ) :
    localZeta μ (0 : K → ℂ) χ s = 0 := by
  simp [localZeta]

def localGammaAt (μ : Measure K) (ψ : AddChar K ℂ) (f₀ : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / localZeta μ f₀ χ s

theorem localGammaAt_eq_zero_of_localZeta_eq_zero {μ : Measure K} {ψ : AddChar K ℂ} {f₀ : K → ℂ}
    {χ : Kˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f₀ χ s = 0) : localGammaAt μ ψ f₀ χ s = 0 := by
  simp [localGammaAt, h]

end Zeta

end LanglandsTunnell.TateLocal

end
