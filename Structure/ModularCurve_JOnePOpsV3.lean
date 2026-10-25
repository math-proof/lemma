import Mathlib
import Structure.ModularCurve_JOnePGeom
import Instance.Compat_Mathlib430

set_option autoImplicit false

namespace ModularCurve

namespace JOneP

variable {p : ℕ}

structure NeronSpecialFibreOpsV3 [NeZero p] (G : NeronSpecialFibreGeom p) where

  hecke : ℕ → (G.J0s →+ G.J0s)
  heckeI : ℕ → (G.JI →+ G.JI)
  heckeE : ℕ → (G.JE →+ G.JE)
  proj_hecke : ∀ (ℓ : ℕ) (x : G.J0s), ℓ ≠ p → G.proj (hecke ℓ x) = (heckeI ℓ (G.proj x).1, heckeE ℓ (G.proj x).2)

  diamondP : (ZMod p)ˣ →* AddAut G.J0s
  diamondN : ℕ → (G.J0s →+ G.J0s)
  w : G.J0s ≃+ G.J0s
  inertia : (ZMod p)ˣ →* AddAut G.J0s

  verI : G.JI →+ G.JI
  frobE : G.JE →+ G.JE
  diamondNI : ℕ → (G.JI →+ G.JI)

  hecke_comm : ∀ ℓ ℓ' : ℕ, (hecke ℓ).comp (hecke ℓ') = (hecke ℓ').comp (hecke ℓ)
  diamondP_hecke : ∀ (b : (ZMod p)ˣ) (ℓ : ℕ) (x : G.J0s), diamondP b (hecke ℓ x) = hecke ℓ (diamondP b x)
  inertia_hecke : ∀ (b : (ZMod p)ˣ) (ℓ : ℕ) (x : G.J0s), inertia b (hecke ℓ x) = hecke ℓ (inertia b x)
  diamondP_torus : ∀ (b : (ZMod p)ˣ) (x : G.J0s), x ∈ G.torus → diamondP b x = x
  inertia_torus : ∀ (b : (ZMod p)ˣ) (x : G.J0s), x ∈ G.torus → inertia b x = x

end JOneP

end ModularCurve
