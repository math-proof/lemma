import Mathlib
import Structure.LatticeTreeOrbital
import Instance.CerednikDrinfeld_BruhatTitsTree

set_option autoImplicit false

namespace CerednikDrinfeld
namespace FormalOmega

structure AlgFunctor (𝒪 : Type) [CommRing 𝒪] : Type 1 where

  obj : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Type

  map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'],
    (B →ₐ[𝒪] B') → obj B → obj B'

  map_id : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] (x : obj B), map (AlgHom.id 𝒪 B) x = x

  map_comp : ∀ {B₁ : Type} [CommRing B₁] [Algebra 𝒪 B₁] {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂]
    {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃] (f : B₁ →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : obj B₁),
    map (g.comp f) x = map g (map f x)

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

structure NatTrans (F G : AlgFunctor 𝒪) : Type 1 where

  app : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], F.obj B → G.obj B

  naturality : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (x : F.obj B), app B' (F.map f x) = G.map f (app B x)


structure GroupAction (Γ : Type) [Group Γ] (F : AlgFunctor 𝒪) : Type 1 where

  act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B
  act_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x = x
  act_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g h : Γ) (x : F.obj B), act B (g * h) x = act B g (act B h x)

  act_map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (g : Γ) (x : F.obj B), F.map f (act B g x) = act B' g (F.map f x)

end AlgFunctor

section Charts

variable (𝒪 : Type) [CommRing 𝒪]


variable {𝒪}


end Charts

section PadicInstance

variable (r : ℕ) [Fact r.Prime]


end PadicInstance

end FormalOmega
end CerednikDrinfeld
