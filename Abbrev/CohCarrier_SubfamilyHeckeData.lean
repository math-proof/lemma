import Lemma.CohCarrier.Inst

set_option autoImplicit false

noncomputable section

namespace CohCarrier

section Sub

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
variable (𝒪 : Type) [CommRing 𝒪] (k : Type) [Field k] [Algebra 𝒪 k]


abbrev MLSubAt [NeZero M] {G : Type} (φ : G → Gen M S)
    (hcomm : ∀ g h : G, opFamily M H S 𝒪 (φ g) * opFamily M H S 𝒪 (φ h) =
      opFamily M H S 𝒪 (φ h) * opFamily M H S 𝒪 (φ g))
    (θbar : G → k) : Type :=
  (hdataSub M H S 𝒪 k φ hcomm θbar).ML

end Sub

end CohCarrier

end
