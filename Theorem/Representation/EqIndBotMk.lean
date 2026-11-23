module

public import Mathlib
public import Theorem.LinearMap.TateCohomology

public section

set_option autoImplicit false
open CategoryTheory


universe u

section
namespace Rep

section DimShift

variable {k G : Type u} [CommRing k] [Group G]


public theorem indBotMk_apply (A : Rep.{u} k G) (g : G) (a : A) :
  A.indBotMk g a = Representation.IndV.mk (⊥ : Subgroup G).subtype (Rep.res (⊥ : Subgroup G).subtype A).ρ g a := rfl

