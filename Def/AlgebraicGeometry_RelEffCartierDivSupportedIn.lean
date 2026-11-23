module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Def.AlgebraicGeometry_RelEffCartierDivFunctor

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ}

def SupportedIn {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) : Prop :=
  (D.I.support : Set ↥(pullback f g)) ⊆ ((pullback.fst f g) ⁻¹ᵁ U : (pullback f g).Opens)

section Locus

variable {T : Scheme.{u}} {g : T ⟶ S}

def supportedInLocus (D : RelEffCartierDiv f r g) (U : 𝒞.Opens) : T.Opens where
  carrier := {t | ∀ z : ↥D.I.subscheme, (D.I.subschemeι ≫ pullback.snd f g) z = t →
    pullback.fst f g (D.I.subschemeι z) ∈ U}
  is_open' := by
    have := D.isFinite
    have hcl : IsClosed ((D.I.subschemeι ≫ pullback.snd f g) ''
        ((D.I.subschemeι ≫ pullback.fst f g) ⁻¹ᵁ U : Set ↥D.I.subscheme)ᶜ) :=
      (D.I.subschemeι ≫ pullback.snd f g).isClosedMap _
        ((D.I.subschemeι ≫ pullback.fst f g) ⁻¹ᵁ U).2.isClosed_compl
    convert hcl.isOpen_compl using 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    exact ⟨fun h z hz hzt => hz (by simpa [Scheme.Hom.comp_apply] using h z hzt),
      fun h z hzt => by
        by_contra hz
        exact h z (by simpa [Scheme.Hom.comp_apply] using hz) hzt⟩

end Locus

variable (f r)

def supportedIn (U : 𝒞.Opens) : Subfunctor (RelEffCartierDiv.functor f r) where
  obj T := {x | x.2.SupportedIn U}
  map {T T'} φ := by
    rintro ⟨g, D⟩ (hD : D.SupportedIn U)
    exact hD.pullbackAlong φ.unop rfl

variable {f r}

end Scheme.RelEffCartierDiv

end
