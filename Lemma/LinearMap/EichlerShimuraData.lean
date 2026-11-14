import Def.HeckeGalois_EichlerShimura
import Abbrev.ModularCurve_EigenformIdeal
import Def.ModularCurve_EichlerShimuraData
import Structure.ModularCurve_EichlerShimuraData

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section TateModule

variable (p : ℕ) {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]


namespace TateModule

variable {p} {J}

lemma mem_iff {x : ℕ → J} :
    x ∈ TateModule p J ↔ x 0 = 0 ∧ ∀ n, p • x (n + 1) = x n :=
  Iff.rfl

lemma pow_smul_apply {x : ℕ → J} (hx : x ∈ TateModule p J) (n : ℕ) :
    p ^ n • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih =>
    have := hx.2 n
    calc p ^ (n + 1) • x (n + 1) = p ^ n • p • x (n + 1) := by
          rw [pow_succ, mul_smul]
      _ = p ^ n • x n := by rw [this]
      _ = 0 := ih

lemma eq_zero_of_pow_smul_eq_zero {x : ℕ → J} (hx : x ∈ TateModule p J) {k : ℕ}
    (h : p ^ k • x = 0) : x = 0 := by

  have key : ∀ m n, x n = p ^ m • x (n + m) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
      intro n
      calc x n = p ^ m • x (n + m) := ih n
        _ = p ^ m • (p • x (n + m + 1)) := by rw [hx.2 (n + m)]
        _ = (p ^ m * p) • x (n + m + 1) := by rw [mul_smul]
        _ = p ^ (m + 1) • x (n + (m + 1)) := by rw [← pow_succ, ← Nat.add_assoc]
  funext n
  have hk : p ^ k • x (n + k) = 0 := by
    have := congrFun h (n + k)
    simpa using this
  simp only [Pi.zero_apply]
  rw [key k n, hk]

omit [SMulCommClass G HeckeAlg J] in

lemma smul_mem (g : G) {x : ℕ → J} (hx : x ∈ TateModule p J) :
    g • x ∈ TateModule p J := by
  refine ⟨by simp [Pi.smul_apply, hx.1], fun n => ?_⟩
  simp only [Pi.smul_apply]
  rw [smul_comm, hx.2 n]

end TateModule


section Bundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [NeZero N] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]


end Bundle

section Torsion

variable (p : ℕ) {J : Type*} [AddCommGroup J]


variable {p}

lemma IsPPowTorsion.zero : IsPPowTorsion p (0 : J) := ⟨0, smul_zero _⟩

lemma IsPPowTorsion.add {x y : J} (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    IsPPowTorsion p (x + y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  refine ⟨m + n, ?_⟩
  have hx' : p ^ (m + n) • x = 0 := by rw [pow_add, mul_comm, mul_smul, hm, smul_zero]
  have hy' : p ^ (m + n) • y = 0 := by rw [pow_add, mul_smul, hn, smul_zero]
  rw [smul_add, hx', hy', add_zero]

lemma IsPPowTorsion.neg {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (-x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [smul_neg, hn, neg_zero]

lemma IsPPowTorsion.sub {x y : J} (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    IsPPowTorsion p (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

private lemma nsmul_galois_smul {G : Type*} [Monoid G] [DistribMulAction G J] (σ : G)
    (m : ℕ) (x : J) : m • (σ • x) = σ • (m • x) := by
  induction m with
  | zero => simp
  | succ m ih => rw [succ_nsmul, succ_nsmul, smul_add, ih]

lemma IsPPowTorsion.galois_smul {G : Type*} [Group G] [DistribMulAction G J] (σ : G)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (σ • x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [nsmul_galois_smul σ (p ^ n) x, hn, smul_zero]

lemma IsPPowTorsion.hecke_smul [Module HeckeAlg J] (t : HeckeAlg)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (t • x) := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg (p ^ n) (t • x), ← mul_smul, mul_comm, mul_smul,
    Nat.cast_smul_eq_nsmul HeckeAlg (p ^ n) x, hn, smul_zero]

lemma IsPPowTorsion.nsmul [Module HeckeAlg J] (m : ℕ)
    {x : J} (hx : IsPPowTorsion p x) : IsPPowTorsion p (m • x) := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x]
  exact hx.hecke_smul _

end Torsion

section Realization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))


namespace IsLambdaAdicRealization

variable {p J k φ V π ρ}
variable (h : IsLambdaAdicRealization p J k φ V π ρ)
include h

lemma map_neg (x : J) (hx : IsPPowTorsion p x) : π (-x) = -π x := by
  have h0 : π (x + -x) = π x + π (-x) := h.map_add x (-x) hx hx.neg
  rw [add_neg_cancel, h.map_zero] at h0
  exact (neg_eq_of_add_eq_zero_right h0.symm).symm

lemma map_sub (x y : J) (hx : IsPPowTorsion p x) (hy : IsPPowTorsion p y) :
    π (x - y) = π x - π y := by
  rw [sub_eq_add_neg, h.map_add x (-y) hx hy.neg, h.map_neg y hy, ← sub_eq_add_neg]

lemma map_nsmul (m : ℕ) (x : J) (hx : IsPPowTorsion p x) : π (m • x) = (m : k) • π x := by
  rw [← Nat.cast_smul_eq_nsmul HeckeAlg m x, h.map_hecke _ x hx, map_natCast]

lemma linearMap_eq_zero (T : V →ₗ[k] V)
    (hT : ∀ x : J, IsPPowTorsion p x → T (π x) = 0) : T = 0 := by
  rw [← LinearMap.ker_eq_top, ← top_le_iff, ← h.spanning, Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  exact hT x hx

lemma linearMap_ext {T₁ T₂ : V →ₗ[k] V}
    (hT : ∀ x : J, IsPPowTorsion p x → T₁ (π x) = T₂ (π x)) : T₁ = T₂ := by
  have key := h.linearMap_eq_zero (T₁ - T₂) fun x hx => by
    rw [LinearMap.sub_apply, hT x hx, sub_self]
  rwa [sub_eq_zero] at key

end IsLambdaAdicRealization

end Realization

section AttachmentData

variable {k : Type*} [Field k]


@[simp] lemma attachmentTraceData_apply_prime (φ : HeckeAlg →+* k) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    attachmentTraceData φ ℓ = φ (heckeGen ⟨ℓ, hℓ⟩) := dif_pos hℓ

end AttachmentData

end ModularCurve

end

end
