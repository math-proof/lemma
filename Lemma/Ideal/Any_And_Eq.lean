import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma pow_sup_eq {B : Type u} [CommRing B] {ι : Type*} [Fintype ι] (b : B) (n : ι → ℕ) (i : ι) : b ^ (Finset.univ.sup n) = b ^ (Finset.univ.sup n - n i) * b ^ (n i) := by
  rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]
private lemma eq_of_pow_smul_eq {B : Type u} [CommRing B] {M : Type u} [AddCommGroup M] [Module B M] (b : B) (h : IsLocalizedModule (Submonoid.powers b) (LinearMap.id : M →ₗ[B] M)) (n : ℕ) (x y : M) (hxy : b ^ n • x = b ^ n • y) : x = y := by
  have hu := h.map_units ⟨b ^ n, n, rfl⟩
  obtain ⟨u, hu⟩ := hu
  have this : (u : Module.End B M) x = (u : Module.End B M) y := by
    rwa [hu]
  have key : ∀ z : M, ((u⁻¹ : (Module.End B M)ˣ) : Module.End B M) ((u : Module.End B M) z) = z := fun z => by
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
  rw [← key x, ← key y, this]
/--
[IsLocalizedModule_exists_forall_isLocalizedModule_comp_eq_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalizedModule_exists_forall_isLocalizedModule_comp_eq_of_span_eq_top.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] {k : ℕ} (f : Fin k → B) (_ : Ideal.span (Set.range f) = ⊤)
  (M : Fin k → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module B (M i)]
  (hM : ∀ i, IsLocalizedModule (Submonoid.powers (f i)) (LinearMap.id : M i →ₗ[B] M i))
  (M₂ : Fin k → Fin k → Type u) [∀ i j, AddCommGroup (M₂ i j)] [∀ i j, Module B (M₂ i j)]
  (ρl : ∀ i j, M i →ₗ[B] M₂ i j) (ρr : ∀ i j, M j →ₗ[B] M₂ i j)
  (hρr : ∀ i j, IsLocalizedModule (Submonoid.powers (f i)) (ρr i j))
  (hdiag : ∀ i, ρl i i = ρr i i)
  (M₃ : Fin k → Fin k → Fin k → Type u) [∀ i j l, AddCommGroup (M₃ i j l)] [∀ i j l, Module B (M₃ i j l)]
  (σ₁ : ∀ i j l, M₂ i j →ₗ[B] M₃ i j l) (σ₂ : ∀ i j l, M₂ i l →ₗ[B] M₃ i j l) (σ₃ : ∀ i j l, M₂ j l →ₗ[B] M₃ i j l)
  (hσ₃ : ∀ i j l, IsLocalizedModule (Submonoid.powers (f i)) (σ₃ i j l))
  (hcoc₁ : ∀ i j l, LinearMap.comp (σ₁ i j l) (ρl i j) = LinearMap.comp (σ₂ i j l) (ρl i l))
  (hcoc₂ : ∀ i j l, LinearMap.comp (σ₁ i j l) (ρr i j) = LinearMap.comp (σ₃ i j l) (ρl j l))
  (hcoc₃ : ∀ i j l, LinearMap.comp (σ₂ i j l) (ρr i l) = LinearMap.comp (σ₃ i j l) (ρr j l)) :
  -- imply
  ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module B N) (π : ∀ i, N →ₗ[B] M i),
    (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (π i)) ∧
    (∀ i j, LinearMap.comp (ρl i j) (π i) = LinearMap.comp (ρr i j) (π j)) := by
  -- proof
  classical
  let N : Submodule B (∀ i, M i) :=
    ⨅ i, ⨅ j, LinearMap.ker (LinearMap.comp (ρl i j) (LinearMap.proj i) - LinearMap.comp (ρr i j) (LinearMap.proj j))
  have hN : ∀ m : ∀ i, M i, m ∈ N ↔ ∀ i j, ρl i j (m i) = ρr i j (m j) := by
    intro m
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, sub_eq_zero]
  let π : ∀ i, N →ₗ[B] M i := fun i => (LinearMap.proj i).comp N.subtype
  have hπ : ∀ i (n : N), π i n = (n : ∀ i, M i) i := fun i n => rfl
  refine ⟨N, inferInstance, inferInstance, π, fun i => ?_, fun i j => ?_⟩
  swap
  ·
    ext n
    simp only [LinearMap.comp_apply, hπ]
    apply (hN n).1 n.2 i j
  refine ⟨fun s => ?_, fun y => ?_, fun {n n'} h => ?_⟩
  ·
    apply (hM i).map_units s
  ·
    have h1 : ∀ j, ∃ (nz : ℕ × M j), f i ^ nz.1 • ρl i j y = ρr i j nz.2 := by
      intro j
      obtain ⟨⟨z, s⟩, hs⟩ := (hρr i j).surj (ρl i j y)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 s.2
      exact ⟨(n, z), by rw [← hs, Submonoid.smul_def, ← hn]⟩
    choose nz hnz using h1
    let N₁ : ℕ := Finset.univ.sup fun j => (nz j).1
    obtain ⟨z', hz'⟩ : ∃ z' : ∀ j, M j, ∀ j, f i ^ N₁ • ρl i j y = ρr i j (z' j) := by
      refine ⟨fun j => f i ^ (N₁ - (nz j).1) • (nz j).2, fun j => ?_⟩
      rw [map_smul, ← hnz j, ← mul_smul, ← pow_sup_eq (f i) (fun j => (nz j).1) j]
    have h2 : ∀ j l, ∃ a : ℕ, f i ^ a • (ρl j l (z' j) - ρr j l (z' l)) = 0 := by
      intro j l
      have hzero : σ₃ i j l (ρl j l (z' j) - ρr j l (z' l)) = 0 := by
        rw [map_sub, sub_eq_zero, ← LinearMap.comp_apply, ← hcoc₂, LinearMap.comp_apply, ← hz' j, map_smul,
          ← LinearMap.comp_apply (σ₁ i j l), hcoc₁, LinearMap.comp_apply,
          ← LinearMap.comp_apply (σ₃ i j l), ← hcoc₃, LinearMap.comp_apply, ← hz' l, map_smul]
      obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f i)) (σ₃ i j l)).1 hzero
      obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      exact ⟨a, by rwa [Submonoid.smul_def, ← ha] at hc⟩
    choose a ha using h2
    let A : ℕ := Finset.univ.sup fun p : Fin k × Fin k => a p.1 p.2
    obtain ⟨w, hwdef⟩ : ∃ w : ∀ j, M j, ∀ j, w j = f i ^ A • z' j := ⟨fun j => f i ^ A • z' j, fun j => rfl⟩
    have hw : w ∈ N := by
      rw [hN]
      intro j l
      rw [hwdef, hwdef, map_smul, map_smul, ← sub_eq_zero, ← smul_sub,
        pow_sup_eq (f i) (fun p : Fin k × Fin k => a p.1 p.2) (j, l), mul_smul, ha j l, smul_zero]
    have hwi : w i = f i ^ (A + N₁) • y := by
      rw [hwdef, pow_add, mul_smul]
      congr 1
      have : ρr i i (z' i) = ρr i i (f i ^ N₁ • y) := by rw [← hz' i, map_smul, hdiag]
      obtain ⟨c, hc⟩ := (hρr i i).exists_of_eq this
      obtain ⟨b, hb⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      rw [Submonoid.smul_def, Submonoid.smul_def, ← hb] at hc
      apply eq_of_pow_smul_eq (f i) (hM i) b _ _ hc
    refine ⟨(⟨w, hw⟩, ⟨f i ^ (A + N₁), _, rfl⟩), ?_⟩
    show f i ^ (A + N₁) • y = w i
    rw [hwi]
  ·
    have h3 : ∀ j, ∃ e : ℕ, f i ^ e • (n : ∀ i, M i) j = f i ^ e • (n' : ∀ i, M i) j := by
      intro j
      have : ρr i j ((n : ∀ i, M i) j) = ρr i j ((n' : ∀ i, M i) j) := by
        rw [← (hN n).1 n.2 i j, ← (hN n').1 n'.2 i j]
        apply congrArg (ρl i j) h
      obtain ⟨c, hc⟩ := (hρr i j).exists_of_eq this
      obtain ⟨e, he⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
      exact ⟨e, by rwa [Submonoid.smul_def, Submonoid.smul_def, ← he] at hc⟩
    choose e he using h3
    refine ⟨⟨f i ^ (Finset.univ.sup e), _, rfl⟩, ?_⟩
    apply Subtype.ext
    funext j
    show f i ^ (Finset.univ.sup e) • (n : ∀ i, M i) j = f i ^ (Finset.univ.sup e) • (n' : ∀ i, M i) j
    rw [pow_sup_eq (f i) e j, mul_smul, mul_smul, he j]


-- created on 2026-10-20
