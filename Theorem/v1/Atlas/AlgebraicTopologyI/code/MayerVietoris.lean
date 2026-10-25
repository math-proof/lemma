/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/MayerVietoris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.MayerVietoris.Part3
open Set Topology EilenbergSteenrod Function

universe u


namespace MayerVietoris

attribute [instance] MayerVietorisCover.instTop

/-- If `g ∘ f` is homotopic to the identity, then on a homology theory `ht.map n g`
is a left inverse of `ht.map n f`, by homotopy invariance and functoriality. -/
lemma hom_inv_id (ht : HomologyTheory) (n : ℤ)
    {P Q : TopPair} (f : MapOfPairs P Q) (g : MapOfPairs Q P)
    (hgf : AreHomotopic (g.comp f) (MapOfPairs.id P)) :
    ∀ x, (ht.map n g) ((ht.map n f) x) = x := by
  have h2 : (ht.map n g).comp (ht.map n f) = AddMonoidHom.id _ := by
    rw [← ht.map_comp, ht.homotopy_invariance n _ _ hgf, ht.map_id]
  intro x; exact congr_fun (congr_arg DFunLike.coe h2) x |>.symm ▸ rfl

/-- If `f` and `g` are pair maps whose compositions are both homotopic to the identity,
then `ht.map n f` is a bijection. This packages the homotopy equivalence into a
bijection on homology, used to transfer information across the excised pair. -/
lemma transfer_bijective (ht : HomologyTheory) (n : ℤ)
    {P Q : TopPair} (f : MapOfPairs P Q) (g : MapOfPairs Q P)
    (hfg : AreHomotopic (f.comp g) (MapOfPairs.id Q))
    (hgf : AreHomotopic (g.comp f) (MapOfPairs.id P)) :
    Bijective (ht.map n f) := by
  constructor
  · intro x y hxy
    have hx := hom_inv_id ht n f g hgf x
    have hy := hom_inv_id ht n f g hgf y
    rw [← hx, ← hy, hxy]
  · intro y
    exact ⟨ht.map n g y, by
      have := hom_inv_id ht n g f hfg y; simpa using this⟩

/-- Exactness transfer along bijective homomorphisms: if `f, g` form an exact sequence at
`B`, `ψ : B ≃+ B'` is a two-sided inverse pair, and `χ : C →+ C'` is injective, then
`(ψ ∘ f, χ ∘ g ∘ ψ⁻¹)` is exact at `B'`. Used to push exactness across the
homotopy equivalences `trSub`, `trSp` in the Mayer-Vietoris construction. -/
lemma exact_transfer_bij {A B C B' C' : Type*}
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup B'] [AddCommGroup C']
    {f : A → B} {g : B → C}
    (he : Exact f g)
    (ψ : B →+ B') (ψ' : B' →+ B) (hψψ' : ∀ y, ψ (ψ' y) = y) (hψ'ψ : ∀ x, ψ' (ψ x) = x)
    (χ : C →+ C') (hχ_inj : Injective χ) :
    Exact (ψ ∘ f) (fun y' => χ (g (ψ' y'))) := by
  intro y'
  constructor
  · intro hy'
    have h1 : g (ψ' y') = 0 := hχ_inj (by rwa [map_zero])
    obtain ⟨x, hx⟩ := (he _).mp h1
    exact ⟨x, show ψ (f x) = y' by rw [hx, hψψ']⟩
  · rintro ⟨x, rfl⟩
    show χ (g (ψ' (ψ (f x)))) = 0
    rw [hψ'ψ, (he (f x)).mpr ⟨x, rfl⟩, map_zero]

end MayerVietoris
