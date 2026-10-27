import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma orbit_map_add [Field F] [AddCommGroup V] [Module F V] [Ring D] [Algebra F D] (ι : D →ₐ[F] Module.End F V) (v : V) (d d' : D) : ι (d + d') v = ι d v + ι d' v := by
  simp [map_add]

private lemma orbit_map_smul [Field F] [AddCommGroup V] [Module F V] [Ring D] [Algebra F D] (ι : D →ₐ[F] Module.End F V) (v : V) (c : F) (d : D) : ι (c • d) v = c • ι d v := by
  simp [map_smul]

private noncomputable def orbit [Field F] [AddCommGroup V] [Module F V] [Ring D] [Algebra F D] (ι : D →ₐ[F] Module.End F V) (v : V) : D →ₗ[F] V := ⟨⟨fun d => ι d v, orbit_map_add ι v⟩, orbit_map_smul ι v⟩

@[simp] lemma orbit_apply [Field F] [AddCommGroup V] [Module F V] [Ring D] [Algebra F D] (ι : D →ₐ[F] Module.End F V) (v : V) (d : D) : orbit ι v d = ι d v := rfl

private lemma orbit_injective [Field F] [AddCommGroup V] [Module F V] [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x) (ι : D →ₐ[F] Module.End F V) {v : V} (hv : v ≠ 0) : Function.Injective (orbit ι v) := by
  rw [injective_iff_map_eq_zero]
  intro d hd
  by_contra hne
  obtain ⟨u, rfl⟩ := hD d hne
  have hu : IsUnit (ι (u : D)) := (Units.isUnit u).map ι
  obtain ⟨w, hw⟩ := hu
  apply hv
  have h1 : (w : Module.End F V) v = 0 := by
    rw [hw]
    apply hd
  calc
    _ = ((w⁻¹ : Units (Module.End F V)) : Module.End F V) ((w : Module.End F V) v) := by
      rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    _ = 0 := by
      rw [h1, map_zero]

private lemma orbit_surjective [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x) (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V) {v : V} (hv : v ≠ 0) : Function.Surjective (orbit ι v) := by
  have hpos : 0 < Module.finrank F V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  let _ : FiniteDimensional F D := Module.finite_of_finrank_pos (hdim ▸ hpos)
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (orbit_injective hD ι hv)

private lemma eq_zero_of_isNilpotent [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Ring D] [Algebra F D] (hD : ∀ x : D, x ≠ 0 → IsUnit x) (ι : D →ₐ[F] Module.End F V) (hdim : Module.finrank F D = Module.finrank F V) {N : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) N) (hN : IsNilpotent N) : N = 0 := by
  obtain hV | hV := subsingleton_or_nontrivial V
  ·
    ext v
    simp [Subsingleton.elim v 0]
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpos : 0 < Module.finrank F V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  have hsurj := orbit_surjective hD ι hdim hv
  have hinj := orbit_injective hD ι hv
  obtain ⟨n₀, hn₀⟩ := hsurj (N v)
  rw [orbit_apply] at hn₀
  have hstep : ∀ d : D, N (ι d v) = ι (d * n₀) v := by
    intro d
    rw [← Module.End.mul_apply, ← (hcomm d).eq, Module.End.mul_apply, ← hn₀, ← Module.End.mul_apply, ← map_mul]
  have key : ∀ k : ℕ, ∀ d : D, (N ^ k) (ι d v) = ι (d * n₀ ^ k) v := by
    intro k
    induction k
    ·
      intro d
      simp
    ·
      rename_i k ih
      intro d
      rw [pow_succ', Module.End.mul_apply, ih, hstep, mul_assoc, ← pow_succ]
  obtain ⟨k, hk⟩ := hN
  have h1 : ι (n₀ ^ k) v = 0 := by
    have := key k 1
    rw [hk, one_mul, LinearMap.zero_apply] at this
    apply this.symm
  have h2 : n₀ ^ k = 0 := by
    apply hinj
    rw [orbit_apply, orbit_apply, map_zero, LinearMap.zero_apply]
    apply h1
  let _ : Nontrivial D := Module.nontrivial_of_finrank_pos (R := F) (hdim ▸ hpos)
  have h3 : n₀ = 0 := by
    by_contra hne
    apply ((hD _ hne).pow k).ne_zero h2
  have hNv : N v = 0 := by
    rw [← hn₀, h3, map_zero, LinearMap.zero_apply]
  ext x
  obtain ⟨d, rfl⟩ := hsurj x
  rw [orbit_apply, LinearMap.zero_apply, ← Module.End.mul_apply, ← (hcomm d).eq, Module.End.mul_apply, hNv, map_zero]

/--
[Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_eq_zero_of_isNilpotent_of_forall_commute_of_forall_isUnit_of_finrank_eq.lean)
-/
@[path]
private lemma main
  [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [Ring D] [Algebra F D]
  (hD : ∀ x : D, x ≠ 0 → IsUnit x)
  (ι : D →ₐ[F] Module.End F V)
  (hdim : Module.finrank F D = Module.finrank F V)
  {N : Module.End F V} (hcomm : ∀ d : D, Commute (ι d) N)
  (hN : IsNilpotent N) :
  -- imply
  N = 0 :=
  eq_zero_of_isNilpotent hD ι hdim hcomm hN


-- created on 2026-10-20
