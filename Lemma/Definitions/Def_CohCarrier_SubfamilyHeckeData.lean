import Lemma.Definitions.Def_CohCarrier_Inst

set_option autoImplicit false

noncomputable section

namespace CohCarrier

section Sub

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]

def hdataSub [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) : HeckeData 𝒪 (H1 M H 𝒪) k where
  Gen := G
  op g := opFamily M H S 𝒪 (φ g)
  comm := hcomm
  θbar := θbar

theorem hdataSub_op [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) (g : G) :
    (hdataSub M H S 𝒪 k φ hcomm θbar).op g = opFamily M H S 𝒪 (φ g) := rfl

theorem hdataSub_id [NeZero M]
    (hcomm : ∀ g h : Gen M S, opFamily M H S 𝒪 g * opFamily M H S 𝒪 h =
      opFamily M H S 𝒪 h * opFamily M H S 𝒪 g)
    (θbar : Gen M S → k) :
    hdataSub M H S 𝒪 k id hcomm θbar = hdata M H S 𝒪 k hcomm θbar := rfl

abbrev MLSubAt [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) : Type :=
  (hdataSub M H S 𝒪 k φ hcomm θbar).ML

example [NeZero M] {G : Type} (φ : G → Gen M S) (hcomm) (θbar : G → k) :
    Module 𝒪 (MLSubAt M H S 𝒪 k φ hcomm θbar) :=
  inferInstance

end Sub

end CohCarrier

end
