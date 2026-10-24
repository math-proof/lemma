import Mathlib
import Lemma.Definitions.Def_Module_CommFamilyAnnPart
import Lemma.Definitions.Def_LaurentSeries_HeckeU
import Lemma.Definitions.Def_LaurentSeries_HeckeV
import Lemma.Definitions.Def_ModularCurve_QExpansionDiff
import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Lemma.Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

open AlgebraicCurve

noncomputable def qExpGens (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) : Option ι → Module.End K (LaurentSeries K)
  | none => LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
  | some i => LaurentSeries.heckeT K (ℓ i) (hℓ i) 2

@[simp] theorem qExpGens_none (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) :
    qExpGens K p ℓ hℓ none = LaurentSeries.heckeU K p (Fact.out : p.Prime).pos := rfl

@[simp] theorem qExpGens_some (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) (i : ι) :
    qExpGens K p ℓ hℓ (some i) = LaurentSeries.heckeT K (ℓ i) (hℓ i) 2 := rfl

noncomputable def mTorsionDiffOf (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {σ : Type*} (F : Module.End.CommFamily K (LaurentSeries K) σ)
    (θbar : σ → K) : Submodule K (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
  regularDifferentials K (modularFunctionFieldC K N) ⊓
    (F.annPart p θbar).comap (qExpansionDiffAlong (modularFunctionFieldC K N).val)

theorem mem_mTorsionDiffOf_iff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {σ : Type*} (F : Module.End.CommFamily K (LaurentSeries K) σ)
    (θbar : σ → K) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    ω ∈ mTorsionDiffOf K p N F θbar ↔
      ω ∈ regularDifferentials K (modularFunctionFieldC K N) ∧
        ∀ Q : MvPolynomial σ (ZMod p),
          MvPolynomial.aeval θbar (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) = 0 →
            F.eval (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q)
              (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) = 0 := by
  rw [mTorsionDiffOf, Submodule.mem_inf, Submodule.mem_comap, Module.End.CommFamily.mem_annPart_iff]

noncomputable def mTorsionDiff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    (hcomm : ∀ a b : Option ι, Commute (qExpGens K p ℓ hℓ a) (qExpGens K p ℓ hℓ b))
    (θbar : Option ι → K) : Submodule K (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
  mTorsionDiffOf K p N (Module.End.CommFamily.mk (qExpGens K p ℓ hℓ) hcomm) θbar

theorem mem_mTorsionDiff_iff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    (hcomm : ∀ a b : Option ι, Commute (qExpGens K p ℓ hℓ a) (qExpGens K p ℓ hℓ b))
    (θbar : Option ι → K) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    ω ∈ mTorsionDiff K p N ℓ hℓ hcomm θbar ↔
      ω ∈ regularDifferentials K (modularFunctionFieldC K N) ∧
        ∀ Q : MvPolynomial (Option ι) (ZMod p),
          MvPolynomial.aeval θbar (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) = 0 →
            (Module.End.CommFamily.mk (qExpGens K p ℓ hℓ) hcomm).eval
                (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q)
              (qExpansionDiffAlong (modularFunctionFieldC K N).val ω) = 0 := by
  rw [mTorsionDiff, mem_mTorsionDiffOf_iff]

end ModularCurve
