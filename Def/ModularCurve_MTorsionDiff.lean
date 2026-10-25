import Mathlib
import Instance.Module_CommFamilyAnnPart
import Lemma.LaurentSeries.HeckeU
import Lemma.LaurentSeries.HeckeV
import Def.ModularCurve_QExpansionDiff
import Def.ModularCurve_JqCoeff
import Def.AlgebraicCurve_RegularDifferentials

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace ModularCurve

open AlgebraicCurve

noncomputable def qExpGens (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] {ι : Type*}
    (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i) : Option ι → Module.End K (LaurentSeries K)
  | none => LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
  | some i => LaurentSeries.heckeT K (ℓ i) (hℓ i) 2


noncomputable def mTorsionDiffOf (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {σ : Type*} (F : Module.End.CommFamily K (LaurentSeries K) σ)
    (θbar : σ → K) : Submodule K (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
  regularDifferentials K (modularFunctionFieldC K N) ⊓
    (F.annPart p θbar).comap (qExpansionDiffAlong (modularFunctionFieldC K N).val)


noncomputable def mTorsionDiff (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] {ι : Type*} (ℓ : ι → ℕ) (hℓ : ∀ i, 0 < ℓ i)
    (hcomm : ∀ a b : Option ι, Commute (qExpGens K p ℓ hℓ a) (qExpGens K p ℓ hℓ b))
    (θbar : Option ι → K) : Submodule K (Ω[↥(modularFunctionFieldC K N)⁄K]) :=
  mTorsionDiffOf K p N (Module.End.CommFamily.mk (qExpGens K p ℓ hℓ) hcomm) θbar

end ModularCurve
