import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {C D : ℕ → Type v}
  [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
  (dC : ∀ n, C n →ₗ[R] C (n + 1)) (dD : ∀ n, D n →ₗ[R] D (n + 1)) (f : ∀ n, C n →ₗ[R] D n)
  (hf : ∀ (n : ℕ) (x : C n), f (n + 1) (dC n x) = dD n (f n x))
  (hdC : ∀ (n : ℕ) (x : C n), dC (n + 1) (dC n x) = 0)
  (hsurj : ∀ n, Function.Surjective (f n))
  (hex0 : ∀ x : C 0, f 0 x = 0 → dC 0 x = 0 → x = 0)
  (hexS : ∀ (n : ℕ) (x : C (n + 1)), f (n + 1) x = 0 → dC (n + 1) x = 0 →
    ∃ y : C n, f n y = 0 ∧ dC n y = x)
include hf
private lemma map_mem_ker (n : ℕ) (x : C n) (hx : x ∈ LinearMap.ker (dC n)) : f n x ∈ LinearMap.ker (dD n) := by
  rw [LinearMap.mem_ker] at hx ⊢
  cases n with
  | zero => rw [← hf, hx, map_zero]
  | succ n => rw [← hf, hx, map_zero]
private noncomputable def kerMap (n : ℕ) : LinearMap.ker (dC n) →ₗ[R] LinearMap.ker (dD n) :=
  (f n).restrict fun x hx => map_mem_ker dC dD f hf n x hx
private lemma kerMap_apply (n : ℕ) (x : LinearMap.ker (dC n)) : (kerMap dC dD f hf n x : D n) = f n x := rfl
include hex0 hdC hsurj hexS in
private lemma kerMap_zero_bijective : Function.Bijective (kerMap dC dD f hf 0) := by
  constructor
  · intro x y hxy
    have h : f 0 (x - y : C 0) = 0 := by
      have := congrArg (fun z : LinearMap.ker (dD 0) => (z : D 0)) hxy
      simp only [kerMap_apply] at this
      rw [map_sub, this, sub_self]
    have hd : dC 0 (x - y : C 0) = 0 := by
      rw [map_sub, (LinearMap.mem_ker.mp x.2), (LinearMap.mem_ker.mp y.2), sub_self]
    have := hex0 _ h hd
    exact Subtype.ext (sub_eq_zero.mp this)
  · intro y
    obtain ⟨x', hx'⟩ := hsurj 0 (y : D 0)
    have h1 : f 1 (dC 0 x') = 0 := by rw [hf, hx', LinearMap.mem_ker.mp y.2]
    obtain ⟨y1, hy1f, hy1d⟩ := hexS 0 (dC 0 x') h1 (hdC 0 x')
    refine ⟨⟨x' - y1, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hy1d, sub_self]
    · apply Subtype.ext
      rw [kerMap_apply]
      change f 0 (x' - y1) = (y : D 0)
      rw [map_sub, hy1f, sub_zero, hx']
abbrev bd (d : ∀ n, C n →ₗ[R] C (n + 1)) (n : ℕ) : Submodule R (LinearMap.ker (d (n + 1))) :=
  (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype
private lemma bd_le_comap (n : ℕ) :
    bd dC n ≤ (bd dD n).comap (kerMap dC dD f hf (n + 1)) := by
  intro x hx
  simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range, kerMap_apply] at hx ⊢
  obtain ⟨w, hw⟩ := hx
  exact ⟨f n w, by rw [← hf, hw]⟩
private noncomputable def quotMap (n : ℕ) :
    (LinearMap.ker (dC (n + 1)) ⧸ bd dC n) →ₗ[R] (LinearMap.ker (dD (n + 1)) ⧸ bd dD n) :=
  Submodule.mapQ (bd dC n) (bd dD n) (kerMap dC dD f hf (n + 1)) (bd_le_comap dC dD f hf n)
private lemma quotMap_mk (n : ℕ) (x : LinearMap.ker (dC (n + 1))) :
    quotMap dC dD f hf n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (kerMap dC dD f hf (n + 1) x) :=
  rfl
include hdC hsurj hexS in
private lemma quotMap_bijective (n : ℕ) : Function.Bijective (quotMap dC dD f hf n) := by
  constructor
  ·
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker, quotMap_mk, Submodule.Quotient.mk_eq_zero] at hq
      simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range, kerMap_apply] at hq
      obtain ⟨z, hz⟩ := hq
      obtain ⟨w, hw⟩ := hsurj n z
      have hfx : f (n + 1) ((x : C (n + 1)) - dC n w) = 0 := by
        rw [map_sub, hf, hw, hz, sub_self]
      have hdx : dC (n + 1) ((x : C (n + 1)) - dC n w) = 0 := by
        rw [map_sub, LinearMap.mem_ker.mp x.2, hdC, sub_zero]
      obtain ⟨y, -, hy⟩ := hexS n _ hfx hdx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_range]
      exact ⟨y + w, by rw [map_add, hy, sub_add_cancel]⟩
  · intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x', hx'⟩ := hsurj (n + 1) (y : D (n + 1))
      have h2 : f (n + 2) (dC (n + 1) x') = 0 := by rw [hf, hx', LinearMap.mem_ker.mp y.2]
      obtain ⟨v, hvf, hvd⟩ := hexS (n + 1) (dC (n + 1) x') h2 (hdC (n + 1) x')
      refine ⟨Submodule.Quotient.mk ⟨x' - v, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, map_sub, hvd, sub_self]
      · rw [quotMap_mk]
        congr 1
        apply Subtype.ext
        rw [kerMap_apply]
        change f (n + 1) (x' - v) = (y : D (n + 1))
        rw [map_sub, hvf, sub_zero, hx']
include hdC hsurj hex0 hexS in
private lemma helper_main :
    (∃ e : LinearMap.ker (dC 0) ≃ₗ[R] LinearMap.ker (dD 0), ∀ x : LinearMap.ker (dC 0), (e x : D 0) = f 0 x) ∧
    ∀ n : ℕ, ∃ e : (LinearMap.ker (dC (n + 1)) ⧸
        (LinearMap.range (dC n)).comap (LinearMap.ker (dC (n + 1))).subtype) ≃ₗ[R]
      (LinearMap.ker (dD (n + 1)) ⧸ (LinearMap.range (dD n)).comap (LinearMap.ker (dD (n + 1))).subtype),
      ∀ (x : LinearMap.ker (dC (n + 1))) (y : LinearMap.ker (dD (n + 1))), (y : D (n + 1)) = f (n + 1) x →
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  refine ⟨⟨LinearEquiv.ofBijective _ (kerMap_zero_bijective dC dD f hf hdC hsurj hex0 hexS), fun x => rfl⟩,
    fun n => ⟨LinearEquiv.ofBijective _ (quotMap_bijective dC dD f hf hdC hsurj hexS n), fun x y hxy => ?_⟩⟩
  rw [LinearEquiv.ofBijective_apply, quotMap_mk]
  congr 1
  exact Subtype.ext hxy.symm
/--
[LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact.lean)
-/
@[path]
private lemma main
    {R : Type u} [CommRing R] {C D : ℕ → Type v}
    [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)] [∀ n, AddCommGroup (D n)] [∀ n, Module R (D n)]
    (dC : ∀ n, C n →ₗ[R] C (n + 1)) (dD : ∀ n, D n →ₗ[R] D (n + 1)) (f : ∀ n, C n →ₗ[R] D n)
    (hf : ∀ (n : ℕ) (x : C n), f (n + 1) (dC n x) = dD n (f n x))
    (hdC : ∀ (n : ℕ) (x : C n), dC (n + 1) (dC n x) = 0)
    (hsurj : ∀ n, Function.Surjective (f n))
    (hex0 : ∀ x : C 0, f 0 x = 0 → dC 0 x = 0 → x = 0)
    (hexS : ∀ (n : ℕ) (x : C (n + 1)), f (n + 1) x = 0 → dC (n + 1) x = 0 →
      ∃ y : C n, f n y = 0 ∧ dC n y = x) :
    (∃ e : LinearMap.ker (dC 0) ≃ₗ[R] LinearMap.ker (dD 0), ∀ x : LinearMap.ker (dC 0), (e x : D 0) = f 0 x) ∧
    ∀ n : ℕ, ∃ e : (LinearMap.ker (dC (n + 1)) ⧸
        (LinearMap.range (dC n)).comap (LinearMap.ker (dC (n + 1))).subtype) ≃ₗ[R]
      (LinearMap.ker (dD (n + 1)) ⧸ (LinearMap.range (dD n)).comap (LinearMap.ker (dD (n + 1))).subtype),
      ∀ (x : LinearMap.ker (dC (n + 1))) (y : LinearMap.ker (dD (n + 1))), (y : D (n + 1)) = f (n + 1) x →
        e (Submodule.Quotient.mk x) = Submodule.Quotient.mk y :=
  helper_main dC dD f hf hdC hsurj hex0 hexS

-- created on 2026-10-20
