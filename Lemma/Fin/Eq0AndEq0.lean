import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w

private lemma Module.End.exists_ne_zero_forall_apply_eq_zero_of_forall_comp_eq_zero
  {R : Type u} [Ring R]
  {V : Type v} [AddCommGroup V] [Module R V] [Nontrivial V]
  {ι : Type w}
  {f : ι → Module.End R V}
  -- given
  (h : ∀ i j, LinearMap.comp (f i) (f j) = 0) :
  -- imply
  ∃ v : V, v ≠ 0 ∧ ∀ i, f i v = 0 := by
  -- proof
  if hall : ∀ i, f i = 0 then
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨v, hv, fun i => by rw [hall i, LinearMap.zero_apply]⟩
  else
    push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hex : ∃ w : V, f i₀ w ≠ 0 := by
      by_contra hw
      push Not at hw
      apply hi₀ (LinearMap.ext hw)
    obtain ⟨w, hw⟩ := hex
    refine ⟨f i₀ w, hw, fun j => ?_⟩
    have := congrArg (fun g : Module.End R V => g w) (h j i₀)
    simpa using this

/--
[FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FixedPart_exists_smul_eq_zero_forall_of_comp_eq_zero.lean)
-/
@[path]
private lemma main
  {T : Type} [CommRing T] [IsReduced T] [IsArtinianRing T]
  {V : Type} [AddCommGroup V] [Module T V]
  {e : V ≃ₗ[T] (Fin 2 → T)}
  {ι : Type}
  {g : ι → V →ₗ[T] V}
  -- given
  (hgg : ∀ i j : ι, LinearMap.comp (g i) (g j) = 0) :
  -- imply
  ∃ v : V, (∀ i : ι, g i v = 0) ∧ ∀ t : T, t • v = 0 → t = 0 := by
  -- proof
  classical
  let g' : ι → (Fin 2 → T) →ₗ[T] (Fin 2 → T) := fun i => LinearMap.comp (LinearMap.comp e.toLinearMap (g i)) e.symm.toLinearMap
  have hgg' : ∀ i j, LinearMap.comp (g' i) (g' j) = 0 := by
    intro i j
    apply LinearMap.ext
    intro x
    have h0 := congrArg (fun f : V →ₗ[T] V => f (e.symm x)) (hgg i j)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h0
    simp only [g', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply, h0, map_zero]
  let M : ι → Matrix (Fin 2) (Fin 2) T := fun i => LinearMap.toMatrix' (g' i)
  have hM : ∀ i j, M i * M j = 0 := by
    intro i j
    simp only [M, ← LinearMap.toMatrix'_comp, hgg', map_zero]
  let φ := IsArtinianRing.equivPi T
  let π : ∀ m : MaximalSpectrum T, T →+* T ⧸ m.asIdeal := fun m => (Pi.evalRingHom _ m).comp φ.toRingEquiv.toRingHom
  have hπφ : ∀ (m : MaximalSpectrum T) (t : T), π m t = φ t m := fun m t => rfl
  let N : ∀ m : MaximalSpectrum T, ι → Matrix (Fin 2) (Fin 2) (T ⧸ m.asIdeal) := fun m i => (M i).map (π m)
  have hN : ∀ m i j, N m i * N m j = 0 := by
    intro m i j
    show (M i).map (π m) * (M j).map (π m) = 0
    rw [← Matrix.map_mul, hM]
    apply Matrix.map_zero _ (map_zero _)
  have hfac : ∀ m : MaximalSpectrum T, ∃ w : Fin 2 → T ⧸ m.asIdeal, w ≠ 0 ∧ ∀ i, Matrix.mulVec (N m i) w = 0 := by
    intro m
    obtain ⟨w, hw, hker⟩ := Module.End.exists_ne_zero_forall_apply_eq_zero_of_forall_comp_eq_zero (f := fun i => Matrix.toLin' (N m i)) (fun i j => by rw [← Matrix.toLin'_mul, hN, map_zero])
    exact ⟨w, hw, fun i => by simpa only [Matrix.toLin'_apply] using hker i⟩
  choose w hw0 hwker using hfac
  let wT : Fin 2 → T := fun k => φ.symm (fun m => w m k)
  have hwT : ∀ (m : MaximalSpectrum T) (k : Fin 2), π m (wT k) = w m k := by
    intro m k
    rw [hπφ]
    simp only [wT, AlgEquiv.apply_symm_apply]
  have hMw : ∀ i, Matrix.mulVec (M i) wT = 0 := by
    intro i
    funext k
    apply φ.injective
    funext m
    rw [Pi.zero_apply, map_zero, Pi.zero_apply, ← hπφ, RingHom.map_mulVec]
    have hcomp : (π m ∘ wT) = w m := funext (hwT m)
    rw [hcomp]
    have hk := congrFun (hwker m i) k
    rwa [Pi.zero_apply] at hk
  refine ⟨e.symm wT, fun i => ?_, fun t ht => ?_⟩
  ·
    have h1 : g' i wT = 0 := by
      rw [← LinearMap.toMatrix'_mulVec (g' i) wT]
      apply hMw i
    have h2 : e (g i (e.symm wT)) = 0 := by
      simpa only [g', LinearMap.comp_apply, LinearEquiv.coe_coe] using h1
    simpa using congrArg e.symm h2
  ·
    have ht' : t • wT = 0 := by
      have := congrArg e ht
      rwa [map_smul, LinearEquiv.apply_symm_apply, map_zero] at this
    apply φ.injective
    rw [map_zero]
    funext m
    rw [Pi.zero_apply, ← hπφ]
    obtain ⟨k, hk⟩ : ∃ k, w m k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hw0 m (funext hcon)
    have hk0 : π m t * π m (wT k) = 0 := by
      rw [← map_mul, ← smul_eq_mul, ← Pi.smul_apply, ht', Pi.zero_apply, map_zero]
    rw [hwT] at hk0
    apply (Iff.mp mul_eq_zero hk0).resolve_right hk


-- created on 2026-10-21
