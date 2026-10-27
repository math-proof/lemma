import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GroupTheory.HNNEmbedding.Part2
open SemidirectProduct
open MathlibExt.GroupTheory.HNNEmbeddingWanted


namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[sigma_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma sigma_of (j : ℤ) : shiftAut (FreeGroup.of j) = FreeGroup.of (j + 1) := by
  unfold shiftAut
  rw [FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
  congr 1

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[sigma_inv_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma sigma_inv_of (j : ℤ) : shiftAut⁻¹ (FreeGroup.of (j + 1)) = FreeGroup.of j := by
  have h : shiftAut (FreeGroup.of j) = FreeGroup.of (j + 1) := sigma_of j
  have h2 := MulAut.inv_apply_self (FreeGroup ℤ) shiftAut (FreeGroup.of j)
  rwa [h] at h2

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[shiftHom_ofAdd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma shiftHom_ofAdd (k : ℤ) : shiftHom (Multiplicative.ofAdd k) = shiftAut ^ k := by
  unfold shiftHom
  rw [zpowersHom_apply]
  congr 1

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[shift_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma shift_formula (k : ℤ) (j : ℤ) :
  (shiftHom (Multiplicative.ofAdd k)) (FreeGroup.of j) = FreeGroup.of (j + k) := by
  rw [shiftHom_ofAdd]
  have gen : ∀ (k : ℤ) (j : ℤ), (shiftAut ^ k) (FreeGroup.of j) = FreeGroup.of (j + k) := by
    intro k
    induction k using Int.induction_on with
    | zero => intro j; simp
    | succ i hi =>
      intro j
      rw [zpow_add_one, MulAut.mul_apply (FreeGroup ℤ), sigma_of, hi, add_assoc]
      congr 1
      ring
    | pred i hi =>
      intro j
      rw [zpow_sub_one, MulAut.mul_apply (FreeGroup ℤ)]
      have hinv : shiftAut⁻¹ (FreeGroup.of j) = FreeGroup.of (j - 1) := by
        have h := sigma_inv_of (j - 1)
        have hj : (j - 1) + 1 = j := by ring
        rwa [hj] at h
      rw [hinv, hi]
      congr 1
      ring
  exact gen k j

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[ofAdd_one_zpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma ofAdd_one_zpow (k : ℤ) :
  (Multiplicative.ofAdd (1:ℤ)) ^ k = Multiplicative.ofAdd k := by
  induction k using Int.induction_on with
  | zero => simp
  | succ i hi => rw [zpow_add_one, hi]; rfl
  | pred i hi => rw [zpow_sub_one, hi]; rfl

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[psiA_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma psiA_of_zero : psiA (FreeGroup.of (0 : Fin 2)) = inl (FreeGroup.of (0:ℤ)) := by
  unfold psiA; rw [FreeGroup.lift_apply_of]; simp

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[psiA_of_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma psiA_of_one : psiA (FreeGroup.of (1 : Fin 2)) = inr
  (Multiplicative.ofAdd (1:ℤ)) := by
  unfold psiA; rw [FreeGroup.lift_apply_of]; simp

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[comp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma comp_eq (G : Type*) [Group G] :
  psiA.comp ((Monoid.Coprod.snd).comp (alpha G)) =
  inl.comp (FreeGroup.map (fun i : ℕ => (-(i : ℤ) : ℤ))) := by
  apply FreeGroup.ext_hom
  intro i
  change psiA (Monoid.Coprod.snd (alpha G (FreeGroup.of i))) = inl
    ((FreeGroup.map _) (FreeGroup.of i))
  rw [FreeGroup.map.of]
  have hα : alpha G (FreeGroup.of i) = (bK G ^ (-(i : ℤ))) * aK G * (bK G ^ ((i : ℤ))) := by
    unfold alpha; rw [FreeGroup.lift_apply_of]
  rw [hα]
  have hsnd : Monoid.Coprod.snd ((bK G ^ (-(i : ℤ))) * aK G * (bK G ^ ((i : ℤ)))) =
    ((FreeGroup.of (1:Fin 2)) ^ (-(i:ℤ))) * (FreeGroup.of (0:Fin 2)) *
      ((FreeGroup.of (1:Fin 2)) ^ ((i:ℤ))) := by
    simp only [map_mul, map_zpow, Monoid.Coprod.snd_apply_inr, aK, bK]
  rw [hsnd]
  have hpsi : psiA (((FreeGroup.of (1:Fin 2)) ^ (-(i:ℤ))) * (FreeGroup.of (0:Fin 2)) *
    ((FreeGroup.of (1:Fin 2)) ^ ((i:ℤ)))) =
    (inr (Multiplicative.ofAdd (1:ℤ)) ^ (-(i:ℤ))) * inl (FreeGroup.of (0:ℤ)) *
      (inr (Multiplicative.ofAdd (1:ℤ)) ^ ((i:ℤ))) := by
    simp only [map_mul, map_zpow, psiA_of_zero, psiA_of_one]
  rw [hpsi]
  have h1 : (inr (Multiplicative.ofAdd (1:ℤ)) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) ^ (-(i:ℤ))
    =
    inr ((Multiplicative.ofAdd (1:ℤ)) ^ (-(i:ℤ))) := by rw [map_zpow]
  have h2 : (inr (Multiplicative.ofAdd (1:ℤ)) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) ^ ((i:ℤ))
    =
    inr ((Multiplicative.ofAdd (1:ℤ)) ^ ((i:ℤ))) := by rw [map_zpow]
  rw [h1, h2, ofAdd_one_zpow, ofAdd_one_zpow]
  have hinv : (inr (Multiplicative.ofAdd (i:ℤ)) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) =
    (inr (Multiplicative.ofAdd (-(i:ℤ))))⁻¹ := by
    have h : Multiplicative.ofAdd (-(i:ℤ)) * Multiplicative.ofAdd (i:ℤ) = 1 := by
      have : (-(i:ℤ)) + (i:ℤ) = 0 := by ring
      have h2 : Multiplicative.ofAdd ((-(i:ℤ)) + (i:ℤ)) = Multiplicative.ofAdd (-(i:ℤ)) *
        Multiplicative.ofAdd (i:ℤ) := rfl
      rw [this] at h2
      have h3 : (Multiplicative.ofAdd (0:ℤ)) = (1 : Multiplicative ℤ) := rfl
      rwa [h3] at h2
    have hS : (inr (Multiplicative.ofAdd (-(i:ℤ))) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) * inr
      (Multiplicative.ofAdd (i:ℤ)) = 1 := by
      rw [← map_mul, h, map_one]
    exact eq_inv_of_mul_eq_one_right hS
  rw [hinv]
  rw [← map_inv]
  rw [← inl_aut]
  rw [shift_formula]
  congr 1
  congr 1
  ring

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[negCast_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma negCast_inj : Function.Injective (fun i : ℕ => (-(i : ℤ) : ℤ)) := by
  intro a b h
  simp only at h
  have h2 : (a : ℤ) = (b : ℤ) := neg_injective h
  exact Nat.cast_injective h2

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[alpha_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma alpha_injective (G : Type*) [Group G] : Function.Injective (alpha G) := by
  have hmap : Function.Injective (FreeGroup.map (fun i : ℕ => (-(i : ℤ) : ℤ))) :=
    FreeGroup.map_injective negCast_inj
  have hRHS : Function.Injective ((SemidirectProduct.inl (N := FreeGroup ℤ) (G := Multiplicative ℤ)
    (φ := shiftHom)).comp (FreeGroup.map (fun i : ℕ => (-(i : ℤ) : ℤ)))) :=
    (SemidirectProduct.inl_injective (N := FreeGroup ℤ) (G := Multiplicative ℤ)
      (φ := shiftHom)).comp hmap
  rw [← comp_eq G] at hRHS
  have hC : Function.Injective ((⇑psiA) ∘ (⇑((Monoid.Coprod.snd).comp (alpha G)))) := hRHS
  have hSnd : Function.Injective (⇑((Monoid.Coprod.snd).comp (alpha G))) :=
    Function.Injective.of_comp hC
  have hSnd2 : Function.Injective ((⇑(Monoid.Coprod.snd)) ∘ (⇑(alpha G))) := hSnd
  exact Function.Injective.of_comp hSnd2

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[psiB_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma psiB_of_zero : psiB (FreeGroup.of (0 : Fin 2)) = inr
  (Multiplicative.ofAdd (1:ℤ)) := by
  unfold psiB; rw [FreeGroup.lift_apply_of]; simp

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[psiB_of_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma psiB_of_one : psiB (FreeGroup.of (1 : Fin 2)) = inl (FreeGroup.of (0:ℤ)) := by
  unfold psiB; rw [FreeGroup.lift_apply_of]; simp

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[comp_eqB](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma comp_eqB (G : Type*) [Group G] (g : ℕ → G) :
  psiB.comp ((Monoid.Coprod.snd).comp (beta G g)) =
  (SemidirectProduct.inl (N := FreeGroup ℤ) (G := Multiplicative ℤ) (φ := shiftHom)).comp
    (FreeGroup.map (fun i : ℕ => (-(i : ℤ) : ℤ))) := by
  apply FreeGroup.ext_hom
  intro i
  simp only [MonoidHom.comp_apply]
  rw [FreeGroup.map.of]
  have hβ : beta G g (FreeGroup.of i) = Monoid.Coprod.inl (g i) *
    ((aK G ^ (-(i : ℤ))) * bK G * (aK G ^ ((i : ℤ)))) := by
    unfold beta; rw [FreeGroup.lift_apply_of]
  rw [hβ]
  have hsnd : Monoid.Coprod.snd (Monoid.Coprod.inl (g i) *
    ((aK G ^ (-(i : ℤ))) * bK G * (aK G ^ ((i : ℤ))))) =
    ((FreeGroup.of (0:Fin 2)) ^ (-(i:ℤ))) * (FreeGroup.of (1:Fin 2)) *
      ((FreeGroup.of (0:Fin 2)) ^ ((i:ℤ))) := by
    simp only [map_mul, map_zpow, Monoid.Coprod.snd_apply_inl, Monoid.Coprod.snd_apply_inr, aK, bK,
      one_mul]
  rw [hsnd]
  have hpsi : psiB (((FreeGroup.of (0:Fin 2)) ^ (-(i:ℤ))) * (FreeGroup.of (1:Fin 2)) *
    ((FreeGroup.of (0:Fin 2)) ^ ((i:ℤ)))) =
    (inr (Multiplicative.ofAdd (1:ℤ)) ^ (-(i:ℤ))) * inl (FreeGroup.of (0:ℤ)) *
      (inr (Multiplicative.ofAdd (1:ℤ)) ^ ((i:ℤ))) := by
    simp only [map_mul, map_zpow, psiB_of_zero, psiB_of_one]
  rw [hpsi]
  have h1 : (inr (Multiplicative.ofAdd (1:ℤ)) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) ^ (-(i:ℤ))
    =
    inr ((Multiplicative.ofAdd (1:ℤ)) ^ (-(i:ℤ))) := by rw [map_zpow]
  have h2 : (inr (Multiplicative.ofAdd (1:ℤ)) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) ^ ((i:ℤ))
    =
    inr ((Multiplicative.ofAdd (1:ℤ)) ^ ((i:ℤ))) := by rw [map_zpow]
  rw [h1, h2, ofAdd_one_zpow, ofAdd_one_zpow]
  have hinv : (inr (Multiplicative.ofAdd (i:ℤ)) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) =
    (inr (Multiplicative.ofAdd (-(i:ℤ))))⁻¹ := by
    have h : Multiplicative.ofAdd (-(i:ℤ)) * Multiplicative.ofAdd (i:ℤ) = 1 := by
      have : (-(i:ℤ)) + (i:ℤ) = 0 := by ring
      have h2 : Multiplicative.ofAdd ((-(i:ℤ)) + (i:ℤ)) = Multiplicative.ofAdd (-(i:ℤ)) *
        Multiplicative.ofAdd (i:ℤ) := rfl
      rw [this] at h2
      have h3 : (Multiplicative.ofAdd (0:ℤ)) = (1 : Multiplicative ℤ) := rfl
      rwa [h3] at h2
    have hS : (inr (Multiplicative.ofAdd (-(i:ℤ))) : FreeGroup ℤ ⋊[shiftHom] Multiplicative ℤ) * inr
      (Multiplicative.ofAdd (i:ℤ)) = 1 := by
      rw [← map_mul, h, map_one]
    exact eq_inv_of_mul_eq_one_right hS
  rw [hinv]
  rw [← map_inv]
  rw [← inl_aut]
  rw [shift_formula]
  congr 1
  congr 1
  ring

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[beta_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma beta_injective (G : Type*) [Group G] (g : ℕ → G) : Function.Injective
  (beta G g) := by
  have hmap : Function.Injective (FreeGroup.map (fun i : ℕ => (-(i : ℤ) : ℤ))) :=
    FreeGroup.map_injective negCast_inj
  have hRHS : Function.Injective ((SemidirectProduct.inl (N := FreeGroup ℤ) (G := Multiplicative ℤ)
    (φ := shiftHom)).comp (FreeGroup.map (fun i : ℕ => (-(i : ℤ) : ℤ)))) :=
    (SemidirectProduct.inl_injective (N := FreeGroup ℤ) (G := Multiplicative ℤ)
      (φ := shiftHom)).comp hmap
  rw [← comp_eqB G g] at hRHS
  have hC : Function.Injective ((⇑psiB) ∘ (⇑((Monoid.Coprod.snd).comp (beta G g)))) := hRHS
  have hSnd : Function.Injective (⇑((Monoid.Coprod.snd).comp (beta G g))) :=
    Function.Injective.of_comp hC
  have hSnd2 : Function.Injective ((⇑(Monoid.Coprod.snd)) ∘ (⇑(beta G g))) := hSnd
  exact Function.Injective.of_comp hSnd2

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[enum_surj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma enum_surj (G : Type*) [Group G] [Countable G] :
  ∃ g : ℕ → G, g 0 = 1 ∧ Function.Surjective g := by
  have hne : Nonempty G := ⟨1⟩
  obtain ⟨e, he⟩ := @exists_surjective_nat G hne _
  refine ⟨fun n => match n with | 0 => 1 | Nat.succ n => e n, rfl, ?_⟩
  intro y
  obtain ⟨n, hn⟩ := he y
  exact ⟨n + 1, hn⟩

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[alpha_x0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma alpha_x0 (G : Type*) [Group G] : alpha G (FreeGroup.of (0:ℕ)) = aK G := by
  have h : alpha G (FreeGroup.of (0:ℕ)) = (bK G ^ (-((0:ℕ) : ℤ))) * aK G *
    (bK G ^ (((0:ℕ) : ℤ))) := by
    unfold alpha
    rw [FreeGroup.lift_apply_of]
  rw [h]
  simp

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[beta_x0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma beta_x0 (G : Type*) [Group G] (g : ℕ → G) (hg0 : g 0 = 1) :
  beta G g (FreeGroup.of (0:ℕ)) = bK G := by
  have h : beta G g (FreeGroup.of (0:ℕ)) = Monoid.Coprod.inl (g 0) *
    ((aK G ^ (-((0:ℕ) : ℤ))) * bK G * (aK G ^ (((0:ℕ) : ℤ)))) := by
    unfold beta
    rw [FreeGroup.lift_apply_of]
  rw [h, hg0]
  simp [aK, bK]

end MathlibExt.GroupTheory.HNNEmbeddingWanted

namespace MathlibExt.GroupTheory.HNNEmbeddingWanted

/--
[higman_neumann_neumann_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/HNNEmbedding.lean)
-/
@[path]
private lemma higman_neumann_neumann_embedding
  {G : Type u} [Group G] [Countable G] :
-- imply
  ∃ (H : Type u) (hH : Group H) (a b : H), letI :=
-- proof
  hH; ∃ (f : G →* H),
    Function.Injective f ∧ Subgroup.closure ({a, b} : Set H) = ⊤ := by
    obtain ⟨g, hg0, hgs⟩ := enum_surj G
    have hα : Function.Injective (alpha G) := alpha_injective G
    have hβ : Function.Injective (beta G g) := beta_injective G g
    let A : Subgroup (K G) := (alpha G).range
    let B : Subgroup (K G) := (beta G g).range
    let φ : A ≃* B := (MonoidHom.ofInjective hα).symm.trans (MonoidHom.ofInjective hβ)
    let HH := HNNExtension (K G) A B φ
    -- t-relation
    have trel : ∀ x : FreeGroup ℕ,
      (HNNExtension.t (A := A) (B := B) (φ := φ) : HH) * HNNExtension.of (A := A) (B := B) (φ := φ)
        (alpha G x) =
      HNNExtension.of (A := A) (B := B) (φ := φ) (beta G g x) * HNNExtension.t (A := A) (B := B)
        (φ := φ) := by
      intro x
      have h := HNNExtension.t_mul_of (A := A) (B := B) (φ := φ) ((MonoidHom.ofInjective hα) x)
      -- h : t * of ↑((ofInjective hα) x) = of ↑(φ ((ofInjective hα) x)) * t
      have h1 : ((MonoidHom.ofInjective hα (f := alpha G)) x).val = alpha G x :=
        MonoidHom.ofInjective_apply hα
      have hφ : φ ((MonoidHom.ofInjective hα (f := alpha G)) x) =
        (MonoidHom.ofInjective hβ (f := beta G g)) x := by
        change ((MonoidHom.ofInjective hα).symm.trans (MonoidHom.ofInjective hβ)) _ = _
        simp
      have h2 : (φ ((MonoidHom.ofInjective hα (f := alpha G)) x)).val = beta G g x := by
        rw [hφ]
        exact MonoidHom.ofInjective_apply hβ
      -- rewrite h using h1 h2
      have h3 : (HNNExtension.t (A := A) (B := B) (φ := φ) : HH) * HNNExtension.of (A := A) (B := B)
        (φ := φ) (((MonoidHom.ofInjective hα (f := alpha G)) x).val) =
        HNNExtension.of (A := A) (B := B) (φ := φ)
          ((φ ((MonoidHom.ofInjective hα (f := alpha G)) x)).val) * HNNExtension.t (A := A)
            (B := B) (φ := φ) := h
      rwa [h1, h2] at h3
    -- values at x0
    have hx0α : alpha G (FreeGroup.of (0:ℕ)) = aK G := alpha_x0 G
    have hx0β : beta G g (FreeGroup.of (0:ℕ)) = bK G := beta_x0 G g hg0
    have trel0 : (HNNExtension.t (A := A) (B := B) (φ := φ) : HH) * HNNExtension.of (A := A) (B := B)
      (φ := φ) (aK G) =
      HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) * HNNExtension.t (A := A) (B := B)
        (φ := φ) := by
      have h := trel (FreeGroup.of (0:ℕ))
      rwa [hx0α, hx0β] at h
    let tH : HH := HNNExtension.t (A := A) (B := B) (φ := φ)
    let aH : HH := HNNExtension.of (A := A) (B := B) (φ := φ) (aK G)
    let bH : HH := HNNExtension.of (A := A) (B := B) (φ := φ) (bK G)
    let C : Subgroup HH := Subgroup.closure ({tH, aH} : Set HH)
    have htC : tH ∈ C := Subgroup.subset_closure (by simp)
    have haC : aH ∈ C := Subgroup.subset_closure (by simp)
    have hb_eq : bH = tH * aH * tH⁻¹ := by
      change HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) = HNNExtension.t (A := A) (B := B)
        (φ := φ) * HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) *
          (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹
      calc HNNExtension.of (A := A) (B := B) (φ := φ) (bK G)
        = (HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) * HNNExtension.t (A := A) (B := B)
          (φ := φ)) * (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹ := by group
        _ = (HNNExtension.t (A := A) (B := B) (φ := φ) * HNNExtension.of (A := A) (B := B) (φ := φ)
          (aK G)) * (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹ := by rw [trel0.symm]
    have hbC : bH ∈ C := by
      rw [hb_eq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htC haC) (Subgroup.inv_mem _ htC)
    -- of (alpha (of i)) and pieces in C
    have of_a_pow : ∀ k : ℤ, HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ k ∈ C := fun k =>
      Subgroup.zpow_mem _ haC k
    have of_b_pow : ∀ k : ℤ, HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^ k ∈ C := fun k =>
      Subgroup.zpow_mem _ hbC k
    have hgi : ∀ i : ℕ, HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inl (g i) : K G) ∈
      C := by
      intro i
      have h := trel (FreeGroup.of i)
      have hαi : alpha G (FreeGroup.of i) = (bK G ^ (-(i:ℤ))) * aK G * (bK G ^ ((i:ℤ))) := by
        unfold alpha; rw [FreeGroup.lift_apply_of]
      have hβi : beta G g (FreeGroup.of i) = Monoid.Coprod.inl (g i) *
        ((aK G ^ (-(i:ℤ))) * bK G * (aK G ^ ((i:ℤ)))) := by
        unfold beta; rw [FreeGroup.lift_apply_of]
      rw [hαi] at h
      rw [hβi] at h
      simp only [map_mul, map_zpow] at h
      -- h : t * (b^(-i) * a * b^(i)) = (inl(gi) * (a^(-i) * b * a^(i))) * t
      -- solve for inl(gi)
      have hQ : HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^ (-(i:ℤ)) * HNNExtension.of
        (A := A) (B := B) (φ := φ) (aK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^
          ((i:ℤ)) ∈ C :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (of_b_pow (-(i:ℤ))) haC) (of_b_pow ((i:ℤ)))
      have hP : HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ (-(i:ℤ)) * HNNExtension.of
        (A := A) (B := B) (φ := φ) (bK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^
          ((i:ℤ)) ∈ C :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (of_a_pow (-(i:ℤ))) hbC) (of_a_pow ((i:ℤ)))
      have hGP : HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inl (g i) : K G) *
        (HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
          (B := B) (φ := φ) (bK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ ((i:ℤ)))
            =
        HNNExtension.t (A := A) (B := B) (φ := φ) *
          (HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
            (B := B) (φ := φ) (aK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^
              ((i:ℤ))) * (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹ := by
        calc HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inl (g i) : K G) *
          (HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
            (B := B) (φ := φ) (bK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^
              ((i:ℤ)))
          = (HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inl (g i) : K G) *
          (HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
            (B := B) (φ := φ) (bK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^
              ((i:ℤ))) * HNNExtension.t (A := A) (B := B) (φ := φ)) *
                (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹ := by group
          _ = (HNNExtension.t (A := A) (B := B) (φ := φ) *
            (HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
              (B := B) (φ := φ) (aK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^
                ((i:ℤ)))) * (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹ := by rw [← h]
      have hG : HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inl (g i) : K G) =
        (HNNExtension.t (A := A) (B := B) (φ := φ) *
          (HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
            (B := B) (φ := φ) (aK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (bK G) ^
              ((i:ℤ))) * (HNNExtension.t (A := A) (B := B) (φ := φ))⁻¹) *
        (HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^ (-(i:ℤ)) * HNNExtension.of (A := A)
          (B := B) (φ := φ) (bK G) * HNNExtension.of (A := A) (B := B) (φ := φ) (aK G) ^
            ((i:ℤ)))⁻¹ := by
        rw [← hGP]
        group
      rw [hG]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htC hQ)
        (Subgroup.inv_mem _ htC)) (Subgroup.inv_mem _ hP)
    have hall_inl : ∀ y : G, HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inl y : K G) ∈
      C := by
      intro y
      obtain ⟨i, hi⟩ := hgs y
      have hm := hgi i
      rwa [hi] at hm
    have hinr : ∀ w : FreeGroup (Fin 2), HNNExtension.of (A := A) (B := B) (φ := φ)
      (Monoid.Coprod.inr w : K G) ∈ C := by
      intro w
      induction w using FreeGroup.induction_on with
      | one =>
        have h1 : HNNExtension.of (A := A) (B := B) (φ := φ)
          (Monoid.Coprod.inr (1 : FreeGroup (Fin 2)) : K G) = 1 := by simp
        rw [h1]
        exact Subgroup.one_mem _
      | of x =>
        fin_cases x
        · exact haC
        · exact hbC
      | inv_of x ih =>
        have hinv : HNNExtension.of (A := A) (B := B) (φ := φ)
          (Monoid.Coprod.inr ((FreeGroup.of x)⁻¹) : K G) =
          (HNNExtension.of (A := A) (B := B) (φ := φ)
            (Monoid.Coprod.inr (FreeGroup.of x) : K G))⁻¹ := by simp
        rw [hinv]
        exact Subgroup.inv_mem _ ih
      | mul x y ihx ihy =>
        have hmul : HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inr (x * y) : K G) =
          HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inr x : K G) *
          HNNExtension.of (A := A) (B := B) (φ := φ) (Monoid.Coprod.inr y : K G) := by simp
        rw [hmul]
        exact Subgroup.mul_mem _ ihx ihy
    have hcoprod : ∀ k : K G, HNNExtension.of (A := A) (B := B) (φ := φ) k ∈ C := by
      intro k
      induction k using Monoid.Coprod.induction_on with
      | inl m => exact hall_inl m
      | inr n => exact hinr n
      | mul x y ihx ihy =>
        have hmul : HNNExtension.of (A := A) (B := B) (φ := φ) (x * y) =
          HNNExtension.of (A := A) (B := B) (φ := φ) x * HNNExtension.of (A := A) (B := B) (φ := φ)
            y := by simp
        rw [hmul]
        exact Subgroup.mul_mem _ ihx ihy
    have htop : C = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro h
      induction h using HNNExtension.induction_on with
      | of g => exact hcoprod g
      | t => exact htC
      | mul x y ihx ihy => exact Subgroup.mul_mem _ ihx ihy
      | inv x ih => exact Subgroup.inv_mem _ ih
    let f : G →* HH := (HNNExtension.of (A := A) (B := B) (φ := φ)).comp Monoid.Coprod.inl
    have hf : Function.Injective f :=
      (HNNExtension.of_injective (A := A) (B := B) φ).comp Monoid.Coprod.inl_injective
    refine ⟨HH, inferInstance, tH, aH, f, hf, ?_⟩
    change Subgroup.closure ({tH, aH} : Set HH) = ⊤
    exact htop
end MathlibExt.GroupTheory.HNNEmbeddingWanted


-- created on 2026-10-20
-- updated on 2026-10-26
