import Mathlib
import Lemma.Definitions.Def_PDivisibleGroup_Basic

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)

abbrev augIdeal (v : ℕ) : Ideal (G.level v) := Hopf.augIdeal R (G.level v)

theorem mem_augIdeal_iff (v : ℕ) (a : G.level v) : a ∈ G.augIdeal v ↔ counit (R := R) a = 0 := Iff.rfl

abbrev Cotangent (v : ℕ) : Type := (G.augIdeal v).Cotangent

theorem augIdeal_le_comap_transition (v : ℕ) :
    G.augIdeal (v + 1) ≤ (G.augIdeal v).comap (G.transitionAlgHom v) := by
  intro a ha
  rw [Ideal.mem_comap, mem_augIdeal_iff, transitionAlgHom_apply, G.counit_transition]
  exact ha

def cotangentMap (v : ℕ) : G.Cotangent (v + 1) →ₗ[R] G.Cotangent v :=
  Ideal.mapCotangent (G.augIdeal (v + 1)) (G.augIdeal v) (G.transitionAlgHom v)
    (G.augIdeal_le_comap_transition v)

@[simp] theorem cotangentMap_toCotangent (v : ℕ) (a : G.augIdeal (v + 1)) :
    G.cotangentMap v ((G.augIdeal (v + 1)).toCotangent a) =
      (G.augIdeal v).toCotangent ⟨G.transition v a, G.augIdeal_le_comap_transition v a.2⟩ := rfl

theorem cotangentMap_surjective (v : ℕ) : Function.Surjective (G.cotangentMap v) := by
  intro y
  obtain ⟨⟨b, hb⟩, rfl⟩ := (G.augIdeal v).toCotangent_surjective y
  obtain ⟨a, rfl⟩ := G.transition_surjective v b

  refine ⟨(G.augIdeal (v + 1)).toCotangent
    ⟨a - algebraMap R _ (counit (R := R) a), Hopf.sub_algebraMap_counit_mem_augIdeal R _ a⟩, ?_⟩
  rw [cotangentMap_toCotangent]
  congr 1
  ext
  change G.transition v (a - algebraMap R _ (counit (R := R) a)) = G.transition v a
  have hb' : counit (R := R) (G.transition v a) = 0 := hb
  rw [G.counit_transition] at hb'
  rw [hb', map_zero, sub_zero]

def HasDimension (n : ℕ) : Prop :=
  ∀ v : ℕ, Nonempty (G.Cotangent v ≃ₗ[R] (Fin n → R ⧸ Ideal.span {(p : R) ^ v}))

theorem hasDimension_zero_of_isIdempotentElem (hI : ∀ v, IsIdempotentElem (G.augIdeal v)) :
    G.HasDimension 0 := by
  intro v
  haveI : Subsingleton (G.Cotangent v) := (Ideal.cotangent_subsingleton_iff _).mpr (hI v)
  exact ⟨LinearEquiv.ofSubsingleton _ _⟩

theorem subsingleton_target_zero (n : ℕ) : Subsingleton (Fin n → R ⧸ Ideal.span {(p : R) ^ 0}) := by
  rw [pow_zero, Ideal.span_singleton_one]
  infer_instance

def cotangentModule : Submodule R (∀ v, G.Cotangent v) where
  carrier := {x | ∀ v, G.cotangentMap v (x (v + 1)) = x v}
  add_mem' {x y} hx hy v := by rw [Pi.add_apply, Pi.add_apply, map_add, hx v, hy v]
  zero_mem' v := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  smul_mem' r x hx v := by rw [Pi.smul_apply, Pi.smul_apply, map_smul, hx v]

theorem mem_cotangentModule_iff (x : ∀ v, G.Cotangent v) :
    x ∈ G.cotangentModule ↔ ∀ v, G.cotangentMap v (x (v + 1)) = x v := Iff.rfl

def cotangentModuleProj (v : ℕ) : G.cotangentModule →ₗ[R] G.Cotangent v where
  toFun x := (x : ∀ v, G.Cotangent v) v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cotangentMap_cotangentModuleProj (v : ℕ) (x : G.cotangentModule) :
    G.cotangentMap v (G.cotangentModuleProj (v + 1) x) = G.cotangentModuleProj v x := x.2 v

abbrev tangentSpace (L : Type) [CommRing L] [Algebra R L] : Type := G.cotangentModule →ₗ[R] L

end PDivisibleGroup

end
