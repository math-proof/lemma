import Mathlib
import Lemma.Definitions.Def_FLTPrelim_FreyPackage
import Lemma.Definitions.Def_FLTPrelim_ModularRep
import Lemma.Definitions.Def_FreyPackage_LevelRaising
import Lemma.Definitions.Def_RibetLevelLowering_ExchangeData

open WeierstrassCurve CuspForm
open scoped CongruenceSubgroup

namespace FreyPackage

def ModularRepOfLevelAt (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → (freyCurveInt P).IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - (((freyCurveInt P).apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def CharacterGroupApparatus (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N q' : ℕ, 0 < N → q.Prime → q'.Prime → q' ≠ q → ¬ q' ∣ N → ¬ q ∣ N →
    P.ModularRepOfLevelNewAt (N * q * q') q' →
    ∃ (k : Type) (hk : Field k) (d : @RibetEndgame.ExchangeData k hk),
      ¬ P.ModularRepOfLevel (N * q') → @RibetEndgame.ExchangeData.SeqIso k hk d

def CharacterGroupApparatusAt (P : FreyPackage) (q : ℕ) : Prop :=
  ∀ N q' : ℕ, 0 < N → q.Prime → q'.Prime → q' ≠ q → ¬ q' ∣ N → ¬ q ∣ N →
    P.ModularRepOfLevelNewAt (N * q * q') q' →
    ∃ (k : Type) (hk : Field k) (d : @RibetEndgame.ExchangeData k hk),
      ¬ P.ModularRepOfLevelAt (N * q') → @RibetEndgame.ExchangeData.SeqIso k hk d

def CharacterGroupApparatusAtFamily (P : FreyPackage) : Prop :=
  ∀ q : ℕ, P.CharacterGroupApparatusAt q

end FreyPackage
