import Mathlib
import Lemma.ModularCurve.ComponentGroupOrder

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open Finset Module

section DifferenceBasis

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

def diffChar (σ : Option κ ≃ ι) (k : κ) : characterLattice ι :=
  ⟨fun x => (if x = σ (some k) then 1 else 0) - (if x = σ none then 1 else 0), by
    rw [mem_characterLattice, Finset.sum_sub_distrib,
      Fintype.sum_ite_eq' (σ (some k)) (fun _ => (1 : ℤ)),
      Fintype.sum_ite_eq' (σ none) (fun _ => (1 : ℤ))]
    norm_num⟩

@[simp] theorem diffChar_coe_apply (σ : Option κ ≃ ι) (k : κ) (x : ι) :
    (diffChar σ k).1 x =
      (if x = σ (some k) then 1 else 0) - (if x = σ none then 1 else 0) :=
  rfl

theorem diffChar_apply_base (σ : Option κ ≃ ι) (k : κ) :
    (diffChar σ k).1 (σ none) = -1 := by
  rw [diffChar_coe_apply, if_pos rfl,
    if_neg (fun h => Option.some_ne_none k (σ.injective h).symm), zero_sub]

theorem diffChar_apply_some (σ : Option κ ≃ ι) (k m : κ) :
    (diffChar σ k).1 (σ (some m)) = if m = k then 1 else 0 := by
  rw [diffChar_coe_apply, if_neg (fun h => Option.some_ne_none m (σ.injective h)), sub_zero]
  by_cases h : m = k
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · rw [if_neg h, if_neg fun hc => h (Option.some_injective κ (σ.injective hc))]

def coordOf (σ : Option κ ≃ ι) : characterLattice ι →ₗ[ℤ] (κ → ℤ) :=
  LinearMap.pi fun k =>
    (LinearMap.proj (σ (some k))).comp (characterLattice ι).subtype

@[simp] theorem coordOf_apply (σ : Option κ ≃ ι) (D : characterLattice ι) (k : κ) :
    coordOf σ D k = D.1 (σ (some k)) :=
  rfl

theorem coe_apply_base_eq_neg_sum (σ : Option κ ≃ ι) (D : characterLattice ι) :
    D.1 (σ none) = - ∑ k : κ, D.1 (σ (some k)) := by
  have hdeg : ∑ o : Option κ, D.1 (σ o) = 0 := by
    rw [Equiv.sum_comp σ (D.1 : ι → ℤ)]
    exact mem_characterLattice.mp D.2
  rw [Fintype.sum_option] at hdeg
  linarith

theorem coordOf_injective (σ : Option κ ≃ ι) : Function.Injective (coordOf σ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  have hsome : ∀ k : κ, D.1 (σ (some k)) = 0 := fun k => congrFun hD k
  have hnone : D.1 (σ none) = 0 := by
    rw [coe_apply_base_eq_neg_sum σ D]
    simp [hsome]
  apply Subtype.ext
  funext x
  obtain ⟨o, rfl⟩ := σ.surjective x
  cases o with
  | none => exact hnone
  | some k => exact hsome k

theorem coordOf_diffChar (σ : Option κ ≃ ι) (k l : κ) :
    coordOf σ (diffChar σ k) l = if l = k then 1 else 0 := by
  rw [coordOf_apply, diffChar_apply_some]

theorem coordOf_surjective (σ : Option κ ≃ ι) : Function.Surjective (coordOf σ) := by
  intro v
  refine ⟨∑ k : κ, v k • diffChar σ k, ?_⟩
  funext l
  rw [map_sum]
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, coordOf_diffChar, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ l v]
  simp

def coordOfEquiv (σ : Option κ ≃ ι) : characterLattice ι ≃ₗ[ℤ] (κ → ℤ) :=
  LinearEquiv.ofBijective (coordOf σ) ⟨coordOf_injective σ, coordOf_surjective σ⟩

@[simp] theorem coordOfEquiv_apply (σ : Option κ ≃ ι) (D : characterLattice ι) :
    coordOfEquiv σ D = coordOf σ D :=
  rfl

def diffBasisOf (σ : Option κ ≃ ι) : Basis κ ℤ (characterLattice ι) :=
  (Pi.basisFun ℤ κ).map (coordOfEquiv σ).symm

theorem diffBasisOf_apply (σ : Option κ ≃ ι) (k : κ) :
    diffBasisOf σ k = diffChar σ k := by
  apply (coordOfEquiv σ).injective
  have h : (coordOfEquiv σ) (diffBasisOf σ k) = Pi.single k 1 := by
    show (coordOfEquiv σ) (((Pi.basisFun ℤ κ).map (coordOfEquiv σ).symm) k) = Pi.single k 1
    rw [Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply]
  rw [h]
  funext l
  rw [coordOfEquiv_apply, coordOf_diffChar, Pi.single_apply]

theorem gramMap_diffChar_diffChar (e : ι → ℕ) (σ : Option κ ≃ ι) (k l : κ) :
    gramMap e (diffChar σ k) (diffChar σ l) =
      (if k = l then (e (σ (some k)) : ℤ) else 0) + (e (σ none) : ℤ) := by
  rw [gramMap_apply]
  have key : ∑ x : ι, (e x : ℤ) * ((diffChar σ k).1 x * (diffChar σ l).1 x) =
      ∑ o : Option κ, (e (σ o) : ℤ) * ((diffChar σ k).1 (σ o) * (diffChar σ l).1 (σ o)) :=
    (Fintype.sum_equiv σ _ _ fun _ => rfl).symm
  rw [key, Fintype.sum_option, diffChar_apply_base, diffChar_apply_base]
  simp_rw [diffChar_apply_some]
  have hsum : ∑ m : κ, (e (σ (some m)) : ℤ) *
      ((if m = k then (1 : ℤ) else 0) * (if m = l then (1 : ℤ) else 0)) =
      if k = l then (e (σ (some k)) : ℤ) else 0 := by
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl]
      have hterm : ∀ m : κ, (e (σ (some m)) : ℤ) *
          ((if m = k then (1 : ℤ) else 0) * (if m = k then (1 : ℤ) else 0)) =
          if m = k then (e (σ (some m)) : ℤ) else 0 := fun m => by
        by_cases hmk : m = k <;> simp [hmk]
      rw [Finset.sum_congr rfl fun m _ => hterm m]
      exact Fintype.sum_ite_eq' k fun m => (e (σ (some m)) : ℤ)
    · rw [if_neg hkl]
      have hterm : ∀ m : κ, (e (σ (some m)) : ℤ) *
          ((if m = k then (1 : ℤ) else 0) * (if m = l then (1 : ℤ) else 0)) = 0 := fun m => by
        by_cases hmk : m = k
        · subst hmk
          simp [hkl]
        · simp [hmk]
      rw [Finset.sum_congr rfl fun m _ => hterm m, Finset.sum_const_zero]
  rw [hsum]
  ring

end DifferenceBasis

section KirchhoffCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def kirchhoffCount (e : ι → ℕ) : ℕ :=
  ∑ x : ι, ∏ y ∈ Finset.univ.erase x, e y

theorem kirchhoffCount_def (e : ι → ℕ) :
    kirchhoffCount e = ∑ x : ι, ∏ y ∈ Finset.univ.erase x, e y :=
  rfl

theorem kirchhoffCount_pos [Nonempty ι] {e : ι → ℕ} (he : ∀ x, 0 < e x) :
    0 < kirchhoffCount e := by
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  rw [kirchhoffCount_def]
  refine Finset.sum_pos' (fun x _ => Nat.zero_le _) ⟨x₀, Finset.mem_univ x₀, ?_⟩
  exact Finset.prod_pos fun y _ => he y

theorem kirchhoffCount_const_one : kirchhoffCount (fun _ : ι => 1) = Fintype.card ι := by
  rw [kirchhoffCount_def]
  trans ∑ _x : ι, 1
  · exact Finset.sum_congr rfl fun x _ => Finset.prod_const_one
  · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

end KirchhoffCount

end ModularCurve
