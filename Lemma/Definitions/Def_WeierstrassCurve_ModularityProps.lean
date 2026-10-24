import Mathlib.NumberTheory.FLT.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Algebra.Algebra.Basic
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace
import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_FLTPrelim_ModularRep
import Lemma.Definitions.Def_FLTPrelim_Modularity

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point

open scoped CongruenceSubgroup

noncomputable section

namespace WeierstrassCurve

open CuspForm ModularFormClass

noncomputable local instance instDecEqQbarNo2Assembly :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def ModRepHasUnipotent (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) n σ - 1)
        * (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) n σ
            - 1) = 0 ∧
      galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) (W.map (Int.castRingHom ℚ)) n σ
          - 1 ≠ 0

def LanglandsTunnellWeightTwo : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 3 →
    W.IsResiduallyModular 3

def ModThreeOrFiveIrreducible (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 → W.IsSemistableModel →
    (W.ModRepIsIrreducible 3 ∨ W.ModRepIsIrreducible 5)

def ThreeFiveSwitchCurve (W : WeierstrassCurve ℤ) : Prop :=
  W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 5 →
    ∃ W' : WeierstrassCurve ℤ, W'.Δ ≠ 0 ∧ W'.IsSemistableModel ∧
      W'.ModRepIsIrreducible 3 ∧ W'.ModRepHasUnipotent 3 ∧
      (¬ W'.IsGoodPrimeFor 3 ∨ ¬ (3 : ℤ) ∣ W'.apOfModel 3) ∧
      ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → W'.IsGoodPrimeFor ℓ → ℓ ≠ 5 →
        (5 : ℤ) ∣ (W'.apOfModel ℓ - W.apOfModel ℓ)

def ModularityLiftingAt (p : ℕ) : Prop :=
  ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible p →
    W.IsResiduallyModular p → W.IsModularModelOfConductorLevel

end WeierstrassCurve

end
