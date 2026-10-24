import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.TateCohomology
open TateCohomology
open Finset CategoryTheory


namespace TateCohomology

/--
[normMap_range_le_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma normMap_range_le_invariants
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep k G} :
-- imply
  LinearMap.range (normMap k G A) ≤ A.ρ.invariants := by
-- proof
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  intro g
  exact Representation.self_norm_apply A.ρ g y

end TateCohomology

namespace TateCohomology

/--
[augmentationSubmodule_le_ker_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma augmentationSubmodule_le_ker_norm
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep k G} :
-- imply
  augmentationSubmodule k G A ≤ LinearMap.ker (normMap k G A) := by
-- proof
  apply Submodule.span_le.mpr
  intro x ⟨g, a, hx⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  subst hx
  simp only [map_sub, normMap, Representation.norm_self_apply, sub_self]

end TateCohomology

namespace TateCohomology

/--
[finite_of_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma finite_of_exact
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  [Finite A]
  [Finite C]
  {f : A →+ B}
  {g : B →+ C}
-- given
  (hex : Function.Exact f g) :
-- imply
  Finite B := by
-- proof
  rw [AddMonoidHom.finite_iff_finite_ker_range g]
  constructor
  · have hker : g.ker = f.range := by
    ext b; constructor
    · intro hb; exact (hex b).mp (AddMonoidHom.mem_ker.mp hb)
    · rintro ⟨a, rfl⟩; exact AddMonoidHom.mem_ker.mpr ((hex (f a)).mpr ⟨a, rfl⟩)
    rwa [hker]
      (fun a => ⟨f a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩)
      (fun ⟨b, hb⟩ => by
        obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp hb
        exact ⟨a, Subtype.ext ha⟩)
  · exact Finite.of_injective Subtype.val Subtype.val_injective

end TateCohomology

namespace TateCohomology

/--
[card_eq_of_exact_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma card_eq_of_exact_pair
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [AddCommGroup A]
  [AddCommGroup B]
  [AddCommGroup C]
  {f : A →+ B}
  {g : B →+ C}
-- given
  (hex : Function.Exact f g) :
-- imply
  Nat.card B = Nat.card f.range * Nat.card g.range := by
-- proof
  have hker : g.ker = f.range := by
    ext b; simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · exact (hex b).mp
    · rintro ⟨a, rfl⟩; exact (hex (f a)).mpr ⟨a, rfl⟩
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv, hker, mul_comm]

end TateCohomology

namespace TateCohomology

/--
[exact_hexagon_card_eq_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma exact_hexagon_card_eq_general
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [AddCommGroup A₁]
  [AddCommGroup A₂]
  [AddCommGroup A₃]
  [AddCommGroup A₄]
  [AddCommGroup A₅]
  [AddCommGroup A₆]
  [Fintype A₁]
  [Fintype A₂]
  [Fintype A₃]
  [Fintype A₄]
  [Fintype A₅]
  [Fintype A₆]
  {f₁ : A₁ →+ A₂}
  {f₂ : A₂ →+ A₃}
  {f₃ : A₃ →+ A₄}
  {f₄ : A₄ →+ A₅}
  {f₅ : A₅ →+ A₆}
  {f₆ : A₆ →+ A₁}
-- given
  (h₁₂ : Function.Exact f₁ f₂)
  (h₂₃ : Function.Exact f₂ f₃)
  (h₃₄ : Function.Exact f₃ f₄)
  (h₄₅ : Function.Exact f₄ f₅)
  (h₅₆ : Function.Exact f₅ f₆)
  (h₆₁ : Function.Exact f₆ f₁) :
-- imply
  Fintype.card A₁ * Fintype.card A₃ * Fintype.card A₅ = Fintype.card A₂ * Fintype.card A₄ * Fintype.card A₆ := by
-- proof
  simp only [Fintype.card_eq_nat_card]
  rw [card_eq_of_exact_pair f₆ f₁ h₆₁, card_eq_of_exact_pair f₁ f₂ h₁₂,
    card_eq_of_exact_pair f₂ f₃ h₂₃, card_eq_of_exact_pair f₃ f₄ h₃₄,
    card_eq_of_exact_pair f₄ f₅ h₄₅, card_eq_of_exact_pair f₅ f₆ h₅₆]
  ring

end TateCohomology

namespace TateCohomology

/--
[tateH0_subsingleton_of_induced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma tateH0_subsingleton_of_induced
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)} :
-- imply
  Subsingleton (tateH0 (Rep.ind (⊥ : Subgroup G).subtype B)) := by
-- proof
  open Representation Finsupp Classical in
  rw [tateH0, Submodule.Quotient.subsingleton_iff]
  ext ⟨v, hv_mem⟩
  simp only [Submodule.mem_top, iff_true]
  rw [normImageInInvariants, Submodule.mem_comap]
  rw [LinearMap.mem_range]
  have coordMap_def : ∀ (h₀ : G) (a : ↑B),
    (Coinvariants.lift _
      (TensorProduct.finsuppScalarLeft k (↑B) G)
      (fun g => by
        have hg : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
        subst hg; simp only [map_one]; exact LinearMap.comp_id _) :
      IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] (G →₀ ↑B))
    (IndV.mk (⊥ : Subgroup G).subtype B.ρ h₀ a) = Finsupp.single h₀ a := by
    intro h₀ a₀
    simp only [Coinvariants.lift_mk, IndV.mk, LinearMap.comp_apply, TensorProduct.mk_apply]
    ext g; simp [Finsupp.single_apply]
  set φ : IndV (⊥ : Subgroup G).subtype B.ρ →ₗ[k] (G →₀ ↑B) :=
    Coinvariants.lift _
      (TensorProduct.finsuppScalarLeft k (↑B) G)
      (fun g => by
        have hg : g = 1 := by ext; exact Subgroup.mem_bot.mp g.2
        subst hg; simp only [map_one]; exact LinearMap.comp_id _)
  have φ_inj : Function.Injective φ := by
    intro v₁ v₂ h
    obtain ⟨x₁, rfl⟩ := Coinvariants.mk_surjective _ v₁
    obtain ⟨x₂, rfl⟩ := Coinvariants.mk_surjective _ v₂
    simp only [φ, Coinvariants.lift_mk] at h
    exact congr_arg _ ((TensorProduct.finsuppScalarLeft k (↑B) G).injective h)
  have φ_mk : ∀ (h₀ : G) (a : ↑B),
    φ (IndV.mk (⊥ : Subgroup G).subtype B.ρ h₀ a) = Finsupp.single h₀ a :=
    coordMap_def
  have eval_equiv : ∀ g₀ : G,
    (Finsupp.lapply (1 : G) : (G →₀ (↑B)) →ₗ[k] ↑B) ∘ₗ φ ∘ₗ
      (B.ρ.ind (⊥ : Subgroup G).subtype g₀) =
    (Finsupp.lapply g₀ : (G →₀ (↑B)) →ₗ[k] ↑B) ∘ₗ φ := by
    intro g₀
    apply IndV.hom_ext; intro h₀; ext a₀
    simp only [LinearMap.comp_apply, φ, Coinvariants.lift_mk, IndV.mk, TensorProduct.mk_apply]
    simp [TensorProduct.finsuppScalarLeft_apply, LinearMap.rTensor_tmul,
      Finsupp.lapply_apply, Finsupp.single_apply, mul_inv_eq_one]
  rw [Representation.mem_invariants] at hv_mem
  have hconst : ∀ g₀ : G, (φ v) g₀ = (φ v) 1 := by
    intro g₀
    have := congr_fun (congr_arg DFunLike.coe (eval_equiv g₀)) v
    simp only [LinearMap.comp_apply, Finsupp.lapply_apply] at this
    rw [hv_mem g₀] at this; exact this.symm
  have norm_eq : ∀ (a₀ : ↑B) (h₀ : G),
    (B.ρ.ind (⊥ : Subgroup G).subtype).norm (IndV.mk _ B.ρ h₀ a₀) =
    ∑ g₀ : G, IndV.mk (⊥ : Subgroup G).subtype B.ρ g₀ a₀ := by
    intro a₀ h₀
    simp only [Representation.norm, LinearMap.sum_apply, ind_mk]
    exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft h₀)) _ _ (fun g => by simp)
  have hv_eq : v = (B.ρ.ind (⊥ : Subgroup G).subtype).norm
    (IndV.mk (⊥ : Subgroup G).subtype B.ρ 1 ((φ v) 1)) := by
    apply φ_inj
    rw [norm_eq, map_sum]
    ext g₀
    simp only [φ_mk]
    simp [hconst g₀]
  exact ⟨_, hv_eq.symm⟩

end TateCohomology

namespace TateCohomology

/--
[tateMinus1_ind_augRetract_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma tateMinus1_ind_augRetract_mk
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  {B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {b : B}
-- given
  (h : G) :
-- imply
  tateMinus1_ind_augRetract B (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ h b) = b := by
-- proof
  simp [tateMinus1_ind_augRetract, Representation.IndV.mk, Representation.Coinvariants.lift_mk,
    Finsupp.linearCombination_single]

end TateCohomology

namespace TateCohomology

/--
[tateMinus1_ind_proj1_mk_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma tateMinus1_ind_proj1_mk_inv
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [DecidableEq G]
  {B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {g : G}
  {b : B} :
-- imply
  tateMinus1_ind_proj1 B (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ g⁻¹ b) = if g = 1 then b else 0 := by
-- proof
  simp only [tateMinus1_ind_proj1, Representation.IndV.mk, LinearMap.comp_apply,
    Representation.Coinvariants.lift_mk, Finsupp.lapply]
  split_ifs with hg
  · subst hg; simp
  · simp [inv_ne_one.mpr hg]

end TateCohomology

namespace TateCohomology

/--
[tateMinus1_ind_proj1_norm_mk1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma tateMinus1_ind_proj1_norm_mk1
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)}
  {b : B} :
-- imply
  tateMinus1_ind_proj1 B ((Representation.ind (⊥ : Subgroup G).subtype B.ρ).norm (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ (1 : G) b)) = b := by
-- proof
  classical
  show tateMinus1_ind_proj1 B
    ((∑ g : G, Representation.ind (⊥ : Subgroup G).subtype B.ρ g)
      (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ 1 b)) = b
  simp only [LinearMap.sum_apply, map_sum, Representation.ind_mk, one_mul]
  simp only [tateMinus1_ind_proj1_mk_inv]
  rw [Finset.sum_ite_eq' Finset.univ (1 : G)]
  simp

end TateCohomology

namespace TateCohomology

/--
[tateMinus1_subsingleton_of_induced](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma tateMinus1_subsingleton_of_induced
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {B : Rep.{u, u, u} k ↥(⊥ : Subgroup G)} :
-- imply
  Subsingleton (tateMinus1 (Rep.ind (⊥ : Subgroup G).subtype B)) := by
-- proof
  classical
  show Subsingleton (LinearMap.ker (normMap k G (Rep.ind (⊥ : Subgroup G).subtype B)) ⧸
    augInKerNorm (Rep.ind (⊥ : Subgroup G).subtype B))
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro ⟨x, hx_ker⟩ _
  change x ∈ augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)
  let r := tateMinus1_ind_augRetract B
  let p := tateMinus1_ind_proj1 B
  let s := Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ (1 : G)
  have hx_norm : normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) x = 0 :=
    LinearMap.mem_ker.mp hx_ker
  have normMap_eq : (Representation.ind (⊥ : Subgroup G).subtype B.ρ).norm =
    normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) := rfl
  have hD : ∀ y : Representation.IndV (⊥ : Subgroup G).subtype B.ρ,
    y - s (r y) ∈ augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B) := by
    suffices h : (augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)).mkQ ∘ₗ
      (LinearMap.id - s ∘ₗ r) = 0 by
      intro y
      have := LinearMap.ext_iff.mp h y
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.zero_apply] at this
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    apply Representation.IndV.hom_ext
    intro h
    ext b
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.zero_apply, Submodule.mkQ_apply]
    change (augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)).mkQ
      (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ h b) -
      (augmentationSubmodule k G (Rep.ind (⊥ : Subgroup G).subtype B)).mkQ
      (s (r (Representation.IndV.mk (⊥ : Subgroup G).subtype B.ρ h b))) = 0
    rw [tateMinus1_ind_augRetract_mk, sub_eq_zero,
      ← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    apply Submodule.subset_span
    exact ⟨h⁻¹, s b, by
      congr 1
      exact ((Representation.ind_mk (⊥ : Subgroup G).subtype B.ρ h⁻¹ 1 b).trans
        (by simp [one_mul])).symm⟩
  have hAug_le_ker := augmentationSubmodule_le_ker_norm (Rep.ind (⊥ : Subgroup G).subtype B)
  have hD_ker : normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) (x - s (r x)) = 0 :=
    LinearMap.mem_ker.mp (hAug_le_ker (hD x))
  have hsr_ker : normMap k G (Rep.ind (⊥ : Subgroup G).subtype B) (s (r x)) = 0 := by
    have h := map_sub (normMap k G (Rep.ind (⊥ : Subgroup G).subtype B)) x (s (r x))
    rw [hx_norm, hD_ker] at h
    simp at h
    exact h
  have hr_zero : r x = 0 := by
    have h1 : p ((Representation.ind (⊥ : Subgroup G).subtype B.ρ).norm (s (r x))) = r x :=
      tateMinus1_ind_proj1_norm_mk1 B (r x)
    rwa [normMap_eq, hsr_ker, map_zero] at h1
  have := hD x
  rwa [hr_zero, map_zero, sub_zero] at this

end TateCohomology

namespace TateCohomology

/--
[card_eq_card_ker_mul_card_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma card_eq_card_ker_mul_card_range
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {f : M →ₗ[R] M} :
-- imply
  Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
-- proof
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker f).toAddSubgroup,
    mul_comm]
  congr 1
  exact Nat.card_congr (f.quotKerEquivRange.toAddEquiv.toEquiv)

end TateCohomology

namespace TateCohomology

/--
[ker_rho_sub_one_eq_invariants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma ker_rho_sub_one_eq_invariants
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep k G}
  {σ : G}
-- given
  (hσ : ∀ x : G, x ∈ Subgroup.zpowers σ) :
-- imply
  LinearMap.ker (A.ρ σ - LinearMap.id) = A.ρ.invariants := by
-- proof
  ext a
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact (A.ρ.mem_invariants_iff_of_forall_mem_zpowers σ hσ a).symm

end TateCohomology

namespace TateCohomology

/--
[rho_pow_sub_mem_range_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma rho_pow_sub_mem_range_nat
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep k G}
  {σ : G}
  {n : ℕ}
  {a : A} :
-- imply
  A.ρ (σ ^ n) a - a ∈ LinearMap.range (A.ρ σ - LinearMap.id) := by
-- proof
  induction n with
  | zero => simp [pow_zero, map_one]
  | succ n ih =>
    set f : Module.End k A := A.ρ σ - LinearMap.id
    have hpow : σ ^ (n + 1) = σ * σ ^ n := by rw [pow_succ']
    have heq : A.ρ (σ ^ (n + 1)) a - a =
      f (A.ρ (σ ^ n) a) + (A.ρ (σ ^ n) a - a) := by
      rw [hpow, A.ρ.map_mul]
      change (A.ρ σ) ((A.ρ (σ ^ n)) a) - a =
        ((A.ρ σ) ((A.ρ (σ ^ n)) a) - (A.ρ (σ ^ n)) a) + ((A.ρ (σ ^ n)) a - a)
      abel
    rw [heq]
    exact Submodule.add_mem _ (LinearMap.mem_range_self _ _) ih

end TateCohomology

namespace TateCohomology

/--
[rho_inv_pow_sub_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma rho_inv_pow_sub_mem_range
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep k G}
  {σ : G}
  {n : ℕ}
  {a : A} :
-- imply
  A.ρ (σ⁻¹ ^ n) a - a ∈ LinearMap.range (A.ρ σ - LinearMap.id) := by
-- proof
  induction n with
  | zero => simp [pow_zero, map_one]
  | succ n ih =>
    set f : Module.End k A := A.ρ σ - LinearMap.id
    have hpow : σ⁻¹ ^ (n + 1) = σ⁻¹ * σ⁻¹ ^ n := by rw [pow_succ']
    have hmul : (A.ρ σ) ((A.ρ σ⁻¹) (A.ρ (σ⁻¹ ^ n) a)) = A.ρ (σ⁻¹ ^ n) a := by
      calc (A.ρ σ) ((A.ρ σ⁻¹) (A.ρ (σ⁻¹ ^ n) a))
        = (A.ρ σ * A.ρ σ⁻¹) (A.ρ (σ⁻¹ ^ n) a) := rfl
        _ = (A.ρ (σ * σ⁻¹)) (A.ρ (σ⁻¹ ^ n) a) := by rw [A.ρ.map_mul]
        _ = (A.ρ 1) (A.ρ (σ⁻¹ ^ n) a) := by rw [mul_inv_cancel]
        _ = A.ρ (σ⁻¹ ^ n) a := by simp [A.ρ.map_one]
    have hinv_in_range :
      A.ρ σ⁻¹ (A.ρ (σ⁻¹ ^ n) a) - A.ρ (σ⁻¹ ^ n) a ∈ LinearMap.range f := by
      set b := A.ρ (σ⁻¹ ^ n) a
      have : A.ρ σ⁻¹ b - b = -(f (A.ρ σ⁻¹ b)) := by
        show (A.ρ σ⁻¹) b - b = -((A.ρ σ) ((A.ρ σ⁻¹) b) - (A.ρ σ⁻¹) b)
        rw [hmul]; abel
      rw [this]
      exact Submodule.neg_mem _ (LinearMap.mem_range_self f _)
    have heq : A.ρ (σ⁻¹ ^ (n + 1)) a - a =
      (A.ρ σ⁻¹ (A.ρ (σ⁻¹ ^ n) a) - A.ρ (σ⁻¹ ^ n) a) + (A.ρ (σ⁻¹ ^ n) a - a) := by
      rw [hpow, A.ρ.map_mul]
      change (A.ρ σ⁻¹) ((A.ρ (σ⁻¹ ^ n)) a) - a = _
      abel
    rw [heq]
    exact Submodule.add_mem _ hinv_in_range ih

end TateCohomology

namespace TateCohomology

/--
[rho_zpow_sub_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma rho_zpow_sub_mem_range
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A : Rep k G}
  {σ : G}
  {n : ℤ}
  {a : A} :
-- imply
  A.ρ (σ ^ n) a - a ∈ LinearMap.range (A.ρ σ - LinearMap.id) := by
-- proof
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact rho_pow_sub_mem_range_nat A σ n a
  | negSucc n =>
    simp only [zpow_negSucc]
    rw [← inv_pow]
    exact rho_inv_pow_sub_mem_range A σ (n + 1) a

end TateCohomology

namespace TateCohomology

/--
[range_rho_sub_one_eq_augmentationSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma range_rho_sub_one_eq_augmentationSubmodule
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [IsCyclic G]
  {A : Rep k G}
  {σ : G}
-- given
  (hσ : ∀ x : G, x ∈ Subgroup.zpowers σ) :
-- imply
  LinearMap.range (A.ρ σ - LinearMap.id) = augmentationSubmodule k G A := by
-- proof
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    apply Submodule.subset_span
    exact ⟨σ, a, rfl⟩
  · unfold augmentationSubmodule
    apply Submodule.span_le.mpr
    intro x ⟨g, a, hx⟩
    rw [hx]
    obtain ⟨n, rfl⟩ := hσ g
    exact rho_zpow_sub_mem_range A σ n a

end TateCohomology

namespace TateCohomology

/--
[card_invariants_mul_augmentation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma card_invariants_mul_augmentation
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [IsCyclic G]
  {A : Rep k G}
  [Finite A] :
-- imply
  Nat.card A = Nat.card A.ρ.invariants * Nat.card (augmentationSubmodule k G A) := by
-- proof
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G)
  set f : Module.End k A := A.ρ σ - LinearMap.id
  have h := card_eq_card_ker_mul_card_range f
  rw [ker_rho_sub_one_eq_invariants A σ hσ,
    range_rho_sub_one_eq_augmentationSubmodule A σ hσ] at h
  exact h

end TateCohomology

namespace TateCohomology

/--
[herbrand_quotient_eq_one_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma herbrand_quotient_eq_one_of_finite
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [IsCyclic G]
  {A : Rep k G}
  [Finite (tateH0 A)]
  [Finite (tateMinus1 A)]
  [Finite A] :
-- imply
  Nat.card (tateH0 A) = Nat.card (tateMinus1 A) := by
-- proof
  set inv := A.ρ.invariants
  set kerN := LinearMap.ker (normMap k G A)
  set ranN := LinearMap.range (normMap k G A)
  set augS := augmentationSubmodule k G A
  set nimI := normImageInInvariants A
  set aikN := augInKerNorm A
  change Nat.card (inv ⧸ nimI) = Nat.card (kerN ⧸ aikN)
  have h1 : Nat.card inv = Nat.card (inv ⧸ nimI) * Nat.card nimI :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup nimI.toAddSubgroup
  have h2 : Nat.card kerN = Nat.card (kerN ⧸ aikN) * Nat.card aikN :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup aikN.toAddSubgroup
  have h3 := card_eq_card_ker_mul_card_range (normMap k G A)
  have h4 := card_invariants_mul_augmentation A
  have h5 : Nat.card nimI = Nat.card ranN :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (normMap_range_le_invariants A)).toEquiv
  have h6 : Nat.card aikN = Nat.card augS :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe (augmentationSubmodule_le_ker_norm A)).toEquiv
  rw [h5] at h1; rw [h6] at h2; rw [h2] at h3; rw [h1] at h4
  have hr : 0 < Nat.card ranN := Nat.card_pos
  have hs : 0 < Nat.card augS := Nat.card_pos
  have key : Nat.card (kerN ⧸ aikN) * (Nat.card ranN * Nat.card augS) =
    Nat.card (inv ⧸ nimI) * (Nat.card ranN * Nat.card augS) := by linarith
  exact (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hr hs) key).symm

end TateCohomology

namespace TateCohomology

/--
[ker_normMap_trivial_int](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma ker_normMap_trivial_int
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀] :
-- imply
  LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ ℤ)) = ⊥ := by
-- proof
  ext n
  simp only [LinearMap.mem_ker, Submodule.mem_bot, normMap, Representation.norm]
  rw [LinearMap.coe_sum, Finset.sum_apply]
  simp only [Representation.trivial_apply]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).elim (absurd · (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) id
  · intro h; rw [h, mul_zero]

end TateCohomology

namespace TateCohomology

/--
[Rep.trivialHom_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma Rep.trivialHom_comp
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [Monoid G₀]
  {M N P : Type}
  [AddCommGroup M]
  [AddCommGroup N]
  [AddCommGroup P]
  {f : M →ₗ[ℤ] N}
  {g : N →ₗ[ℤ] P} :
-- imply
  Rep.trivialHom (G₀ := G₀) f ≫ Rep.trivialHom g = Rep.trivialHom (g.comp f) := by
-- proof
  ext x; simp [Rep.trivialHom, Rep.ofHom]

end TateCohomology

namespace TateCohomology

/--
[Rep.trivialHom_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma Rep.trivialHom_id
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  [Monoid G₀]
  {M : Type}
  [AddCommGroup M] :
-- imply
  Rep.trivialHom (G₀ := G₀) (LinearMap.id (M := M) (R := ℤ)) = 𝟙 _ := by
-- proof
  ext x; simp [Rep.trivialHom, Rep.ofHom]

end TateCohomology

namespace TateCohomology

/--
[finite_kernel_of_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma finite_kernel_of_mono
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {A B : Rep k G}
  {ι : B ⟶ A}
  [Mono ι] :
-- imply
  Finite (Limits.kernel ι : Rep k G) := by
-- proof
  have hz := Limits.isZero_kernel_of_mono ι
  haveI : Subsingleton (Limits.kernel ι : Rep k G) := by
    constructor
    intro a b
    have : ∀ x : (Limits.kernel ι : Rep k G), x = 0 := by
      intro x
      have key := congr_arg (fun g => (show Limits.kernel ι ⟶ Limits.kernel ι from g).hom)
        (hz.eq_of_src (𝟙 (Limits.kernel ι)) 0)
      have := congr_fun (congr_arg DFunLike.coe key) x
      simpa using this
    rw [this a, this b]
  exact Finite.of_subsingleton

end TateCohomology

namespace TateCohomology

/--
[card_tateMinus1_trivial_finFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma card_tateMinus1_trivial_finFun
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  [IsCyclic G₀]
  {n : ℕ}
  [Fintype (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ)))] :
-- imply
  Fintype.card (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) = 1 := by
-- proof
  haveI : Subsingleton (LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ)))) := by
    rw [ker_normMap_trivial_finFun n]; infer_instance
  haveI : Subsingleton (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ))) :=
    Quotient.instSubsingletonQuotient _
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    |>.antisymm (Fintype.card_pos)

end TateCohomology

namespace TateCohomology

/--
[card_tateH0_trivial_finFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma card_tateH0_trivial_finFun
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  [IsCyclic G₀]
  {n : ℕ}
  [Fintype (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)))] :
-- imply
  Fintype.card (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ))) = Fintype.card G₀ ^ n := by
-- proof
  rw [Fintype.card_congr (tateH0_equiv_pi_zmod n), Fintype.card_fun, ZMod.card, Fintype.card_fin]

end TateCohomology

namespace TateCohomology

/--
[herbrandQuotient_trivial_finFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
lemma herbrandQuotient_trivial_finFun
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  [IsCyclic G₀]
  {n : ℕ}
  [Fintype (tateH0 (Rep.trivial ℤ G₀ (Fin n → ℤ)))]
  [Fintype (tateMinus1 (Rep.trivial ℤ G₀ (Fin n → ℤ)))] :
-- imply
  herbrandQuotient (Rep.trivial ℤ G₀ (Fin n → ℤ)) = (Fintype.card G₀ : ℚ) ^ n := by
-- proof
  simp only [herbrandQuotient,
    card_tateH0_trivial_finFun G₀ n, card_tateMinus1_trivial_finFun G₀ n,
    Nat.cast_one, div_one, Nat.cast_pow]

end TateCohomology

/--
[invEquivTrivInt_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
private lemma invEquivTrivInt_apply_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  {x : (Rep.trivial ℤ G₀ ℤ).ρ.invariants} :
-- imply
  (invEquivTrivInt (G₀ := G₀)) x = x.1 := by
-- proof
  apply TateCohomology.invEquivTrivInt_apply x

/--
[map_normImage_trivInt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
private lemma map_normImage_trivInt_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀] :
-- imply
  Submodule.map (invEquivTrivInt (G₀ := G₀)).toLinearMap (normImageInInvariants (Rep.trivial ℤ G₀ ℤ)) = Submodule.span ℤ {(Fintype.card G₀ : ℤ)} := by
-- proof
  apply TateCohomology.map_normImage_trivInt

/--
[ker_normMap_trivial_finFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
private lemma ker_normMap_trivial_finFun_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  {n : ℕ} :
-- imply
  LinearMap.ker (normMap ℤ G₀ (Rep.trivial ℤ G₀ (Fin n → ℤ))) = ⊥ := by
-- proof
  apply TateCohomology.ker_normMap_trivial_finFun n

/--
[invEquivTrivFinFun_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
private lemma invEquivTrivFinFun_apply_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  {n : ℕ}
  {x : (Rep.trivial ℤ G₀ (Fin n → ℤ)).ρ.invariants} :
-- imply
  (invEquivTrivFinFun n (G₀ := G₀)) x = x.1 := by
-- proof
  apply TateCohomology.invEquivTrivFinFun_apply n x

/--
[map_normImage_trivFinFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
private lemma map_normImage_trivFinFun_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  {n : ℕ} :
-- imply
  Submodule.map (invEquivTrivFinFun n (G₀ := G₀)).toLinearMap (normImageInInvariants (Rep.trivial ℤ G₀ (Fin n → ℤ))) = LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) := by
-- proof
  apply TateCohomology.map_normImage_trivFinFun n

/--
[range_smul_id_eq_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TateCohomology.lean)
-/
@[path]
private lemma range_smul_id_eq_pi_eq
  {k : Type u}
  [CommRing k]
  {G : Type u}
  [Group G]
  [Fintype G]
  {G₀ : Type}
  [Group G₀]
  [Fintype G₀]
  {n : ℕ} :
-- imply
  LinearMap.range ((Fintype.card G₀ : ℤ) • LinearMap.id (R := ℤ) (M := Fin n → ℤ)) = Submodule.pi Set.univ (fun _ : Fin n => Submodule.span ℤ {(Fintype.card G₀ : ℤ)}) := by
-- proof
  apply TateCohomology.range_smul_id_eq_pi n


-- created on 2026-10-23
