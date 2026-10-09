import Mathlib
import sympy.Basic

universe u v w
set_option maxHeartbeats 800000
set_option autoImplicit false

open Polynomial

namespace AdjoinRootPointsAux

variable (W₀ : Type u) {S : Type v} [CommRing W₀] [CommRing S] [Algebra W₀ S] (g : S[X])
  (T : Type w) [CommRing T] [Algebra W₀ T]

abbrev Pts : Type _ := {p : (S →ₐ[W₀] T) × T // (g.map (p.1 : S →+* T)).eval p.2 = 0}

variable {T}

theorem eval_map_apply_root (χ : AdjoinRoot g →ₐ[W₀] T) :
    (g.map ((χ.comp (AdjoinRoot.ofAlgHom W₀ g) : S →ₐ[W₀] T) : S →+* T)).eval
      (χ (AdjoinRoot.root g)) = 0 := by
  rw [← Polynomial.eval₂_eq_eval_map]
  show g.eval₂ ((χ : AdjoinRoot g →+* T).comp (AdjoinRoot.of g))
    ((χ : AdjoinRoot g →+* T) (AdjoinRoot.root g)) = 0
  rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

noncomputable def toPts (χ : AdjoinRoot g →ₐ[W₀] T) : Pts W₀ g T :=
  ⟨(χ.comp (AdjoinRoot.ofAlgHom W₀ g), χ (AdjoinRoot.root g)), eval_map_apply_root W₀ g χ⟩

theorem toPts_fst (χ : AdjoinRoot g →ₐ[W₀] T) :
    (toPts W₀ g χ).1.1 = χ.comp (AdjoinRoot.ofAlgHom W₀ g) := rfl

theorem toPts_snd (χ : AdjoinRoot g →ₐ[W₀] T) :
    (toPts W₀ g χ).1.2 = χ (AdjoinRoot.root g) := rfl

theorem eval₂_eq_zero_of_pts (p : Pts W₀ g T) :
    g.eval₂ (p.1.1 : S →ₐ[W₀] T) p.1.2 = 0 := by
  have := p.2
  rwa [← Polynomial.eval₂_eq_eval_map] at this

noncomputable def ofPts (p : Pts W₀ g T) : AdjoinRoot g →ₐ[W₀] T :=
  AdjoinRoot.liftAlgHom g p.1.1 p.1.2 (eval₂_eq_zero_of_pts W₀ g p)

theorem ofPts_of (p : Pts W₀ g T) (s : S) :
    ofPts W₀ g p (AdjoinRoot.of g s) = p.1.1 s :=
  AdjoinRoot.liftAlgHom_of g _ _ _ s

theorem ofPts_root (p : Pts W₀ g T) :
    ofPts W₀ g p (AdjoinRoot.root g) = p.1.2 :=
  AdjoinRoot.liftAlgHom_root g _ _ _

theorem ofPts_toPts (χ : AdjoinRoot g →ₐ[W₀] T) :
    ofPts W₀ g (toPts W₀ g χ) = χ := by
  refine AdjoinRoot.algHom_ext' ?_ ?_
  · ext s
    exact ofPts_of W₀ g (toPts W₀ g χ) s
  · exact ofPts_root W₀ g (toPts W₀ g χ)

theorem toPts_ofPts (p : Pts W₀ g T) : toPts W₀ g (ofPts W₀ g p) = p := by
  apply Subtype.ext
  apply Prod.ext
  · ext s
    exact ofPts_of W₀ g p s
  · exact ofPts_root W₀ g p

noncomputable def equiv : (AdjoinRoot g →ₐ[W₀] T) ≃ Pts W₀ g T where
  toFun := toPts W₀ g
  invFun := ofPts W₀ g
  left_inv := ofPts_toPts W₀ g
  right_inv := toPts_ofPts W₀ g

theorem equiv_naturality {T' : Type w} [CommRing T'] [Algebra W₀ T'] (f : T →ₐ[W₀] T')
    (χ : AdjoinRoot g →ₐ[W₀] T) :
    ((equiv W₀ g (f.comp χ)).1.1 = f.comp (equiv W₀ g χ).1.1) ∧
      (equiv W₀ g (f.comp χ)).1.2 = f ((equiv W₀ g χ).1.2) :=
  ⟨rfl, rfl⟩

end AdjoinRootPointsAux

/-- Embedding of `S` into `AdjoinRoot g` as a `Λ`-algebra homomorphism. -/
noncomputable abbrev AdjoinRoot.toAlgHom
  (Λ : Type u) [CommRing Λ] {S : Type v} [CommRing S] [Algebra Λ S]
  (g : Polynomial S) : S →ₐ[Λ] AdjoinRoot g :=
  AdjoinRoot.ofAlgHom Λ g

/--
[AdjoinRoot_exists_algHom_equiv_subtype_eval_map_eq_zero_natural](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdjoinRoot_exists_algHom_equiv_subtype_eval_map_eq_zero_natural.lean)
-/
@[path]
private lemma main
  {Λ : Type u} [CommRing Λ]
-- given
  (S : Type v) [CommRing S] [Algebra Λ S] (g : Polynomial S) :
-- imply
  ∃ η : ∀ (T : Type w) [CommRing T] [Algebra Λ T],
        ((AdjoinRoot g →ₐ[Λ] T) ≃ {p : (S →ₐ[Λ] T) × T // (g.map (p.1 : S →+* T)).eval p.2 = 0}),
      (∀ (T : Type w) [CommRing T] [Algebra Λ T] (φ : AdjoinRoot g →ₐ[Λ] T),
        ((η T φ).1 : (S →ₐ[Λ] T) × T) =
          (φ.comp (AdjoinRoot.toAlgHom Λ g), φ (AdjoinRoot.root g))) ∧
      ∀ (T : Type w) [CommRing T] [Algebra Λ T] (T' : Type w) [CommRing T'] [Algebra Λ T']
        (f : T →ₐ[Λ] T') (φ : AdjoinRoot g →ₐ[Λ] T),
        ((η T' (f.comp φ)).1 : (S →ₐ[Λ] T') × T') = (f.comp (η T φ).1.1, f (η T φ).1.2) :=
-- proof
  ⟨fun T _ _ => AdjoinRootPointsAux.equiv Λ g (T := T),
    fun _ _ _ _ => rfl,
    fun _ _ _ _ _ _ _ _ => rfl⟩


-- created on 2026-10-09
