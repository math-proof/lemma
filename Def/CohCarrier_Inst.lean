import Def.CohCarrier_Level
import Lemma.MvPolynomial.HeckeData
import Inductive.CohCarrier_Gen

set_option autoImplicit false

noncomputable section

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

section Inst

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

def heckeTL (ℓ : ℕ) [NeZero ℓ] : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := coresAdd _ (φ.comp (MonoidHom.toAdditive (conjL M H ℓ)))
  map_add' φ ψ := by
    have : (φ + ψ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) + ψ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : (r • φ).comp (MonoidHom.toAdditive (conjL M H ℓ)) =
        r • φ.comp (MonoidHom.toAdditive (conjL M H ℓ)) := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

def diamondL [NeZero M] (d : (ZMod M)ˣ) : Module.End 𝒪 (H1 M H 𝒪) where
  toFun φ := diamondRaw M H 𝒪 (Classical.choose (gamma0Units_surjective M d)) φ
  map_add' φ ψ := map_add _ φ ψ
  map_smul' r φ := by ext; rfl

def opFamily [NeZero M] : Gen M S → Module.End 𝒪 (H1 M H 𝒪)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeTL M H 𝒪 ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeTL M H 𝒪 q
  | .dia d => diamondL M H 𝒪 d

def hdata [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) : HeckeData 𝒪 (H1 M H 𝒪) k where
  Gen := Gen M S
  op := opFamily M H S 𝒪
  comm := hcomm
  θbar := θbar

abbrev MLAt [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) : Type :=
  (hdata M H S 𝒪 k hcomm θbar).ML

end Inst

end CohCarrier

end
