import Mathlib
import sympy.Basic

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

-- Mathlib Point AddCommGroup needs DecidableEq on the base field.
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

namespace ValuationSubring

/-- Valuation ring lies over the prime ideal (q). -/
def LiesOverPrime {L : Type*} [Field L] (A : ValuationSubring L) (q : ℕ) : Prop :=
  (q : L) ∈ A.nonunits

/-- Inertia subgroup of A inside L ≃ₐ[K] L. -/
noncomputable def inertiaSubgroupIn (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype

end ValuationSubring

namespace WeierstrassCurve.Affine.Point

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

noncomputable instance : SMul (K ≃ₐ[S] K) (W'⁄K).Point :=
  ⟨fun σ P => Point.map σ.toAlgHom P⟩

noncomputable instance : DistribMulAction (K ≃ₐ[S] K) (W'⁄K).Point where
  one_smul P := by cases P <;> rfl
  mul_smul σ τ P := by cases P <;> rfl
  smul_zero _ := rfl
  smul_add σ P Q := (Point.map σ.toAlgHom).map_add P Q

private lemma algEquiv_smul_zsmul (σ : K ≃ₐ[S] K) (m : ℤ) (P : (W'⁄K).Point) :
    σ • (m • P) = m • (σ • P) :=
  (Point.map σ.toAlgHom).map_zsmul m P

end WeierstrassCurve.Affine.Point


/--
[AddSubgroup_eq_atP_filtration_of_cyclic_stable_inertia_nontrivial](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_eq_atP_filtration_of_cyclic_stable_inertia_nontrivial.lean)
-/

private lemma zsmul_pow_nat_eq_zero {P : Type*} [AddCommGroup P] {p m : ℕ}
  {x : P} (hx : p ^ m • x = 0) : ((p : ℤ) ^ m) • x = 0 := by
  have : ((p : ℤ) ^ m) = ((p ^ m : ℕ) : ℤ) := by push_cast; ring
  rw [this, natCast_zsmul, hx]
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {W : WeierstrassCurve ℤ}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  {m : ℕ}
  {K F : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point}
-- given
  (hA : A.LiesOverPrime p)
  (hm : 1 ≤ m)
  (hKcard : Nat.card K = p ^ m)
  (hK1 : IsAddCyclic K)
  (hKtors : ∀ x ∈ K, p ^ m • x = 0)
  (hKstab : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ K, σ • x ∈ K)
  (hNontriv : ∃ τ ∈ A.inertiaSubgroupIn ℚ, ∃ x ∈ K, p • x = 0 ∧ τ • x ≠ x)
  (hFabs : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point, p ^ m • y = 0 → σ • y - y ∈ F) :
-- imply
  K ≤ F := by
-- proof
  have hp : p.Prime := Fact.out

  have _ := hA; have _ := hm; have _ := hKcard
  by_contra hKF

  obtain ⟨τ, hτ, x₀, hx₀K, hpx₀, hτx₀⟩ := hNontriv

  obtain ⟨g, hg⟩ := hK1.exists_generator
  set k := (g : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
  have hkK : k ∈ K := g.2

  have hKk : ∀ y ∈ K, ∃ n : ℤ, n • k = y := by
    intro y hy
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨y, hy⟩)
    refine ⟨n, ?_⟩
    have := congrArg (K.subtype) hn
    simpa using this

  have hkF : k ∉ F := by
    intro hkF
    apply hKF
    intro y hy
    obtain ⟨n, rfl⟩ := hKk y hy
    exact F.zsmul_mem hkF n

  have hk0 : ((p : ℤ) ^ m) • k = 0 := zsmul_pow_nat_eq_zero (hKtors k hkK)

  obtain ⟨a, ha⟩ := hKk (τ • k) (hKstab τ hτ k hkK)

  have hdiffF : (a - 1) • k ∈ F := by
    have h1 : (a - 1) • k = τ • k - k := by
      rw [sub_zsmul, one_zsmul, ha, ← sub_eq_add_neg]
    rw [h1]
    exact hFabs τ hτ k (hKtors k hkK)

  have hpdvd : (p : ℤ) ∣ (a - 1) := by
    by_contra hnd
    have hcop : IsCoprime ((p : ℤ) ^ m) (a - 1) :=
      (((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd).mpr hnd).pow_left
    obtain ⟨u, v, huv⟩ := hcop

    have hkeq : k = v • ((a - 1) • k) := calc
      _ = (1 : ℤ) • k := (one_zsmul k).symm
      _ = (u * (p : ℤ) ^ m + v * (a - 1)) • k := by rw [huv]
      _ = u • ((p : ℤ) ^ m • k) + v • ((a - 1) • k) := by
          rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = v • ((a - 1) • k) := by rw [hk0, zsmul_zero, zero_add]
    exact hkF (hkeq ▸ F.zsmul_mem hdiffF v)

  obtain ⟨b, rfl⟩ := hKk x₀ hx₀K
  have hτx₀eq : τ • (b • k) = a • (b • k) := by
    rw [algEquiv_smul_zsmul, ← ha]; exact zsmul_comm k a b

  obtain ⟨d, hd⟩ := hpdvd
  apply hτx₀
  have hkey : (a - 1) • (b • k) = 0 := by
    rw [hd, mul_comm, mul_zsmul, natCast_zsmul, hpx₀, zsmul_zero]
  rw [hτx₀eq]
  calc _ = (a - 1) • (b • k) + (1 : ℤ) • (b • k) := by
        rw [← add_zsmul, sub_add_cancel]
    _ = b • k := by rw [hkey, zero_add, one_zsmul]


-- created on 2026-10-09
