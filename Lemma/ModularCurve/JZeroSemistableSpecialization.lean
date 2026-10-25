import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.GluedPic0Functoriality
import Lemma.ModularCurve.ArithmeticGalois
import Lemma.ModularCurve.JqCoeff
import Def.HeckeGalois_EichlerShimura
import Lemma.ModularCurve.ComponentGroup
import Instance.ModularCurve_JZeroSemistableSpecialization
import Structure.ModularCurve_JZeroSemistableSpecialization
import Notation.ModularCurve_JZeroSemistableSpecialization

noncomputable section

namespace ModularCurve

open AlgebraicCurve IsLocalRing

open scoped ModularCurve_JZeroSemistableSpecialization

section Generic


namespace PrimeToTorsion

variable {q : ℕ} {M M' : Type*}

theorem zero [AddMonoid M] (hq : q ≠ 1) : PrimeToTorsion q (0 : M) :=
  ⟨1, Nat.one_pos, fun h => hq (Nat.dvd_one.mp h), nsmul_zero _⟩

theorem add [AddCommMonoid M] (hq : q.Prime) {x y : M} (hx : PrimeToTorsion q x)
    (hy : PrimeToTorsion q y) : PrimeToTorsion q (x + y) := by
  obtain ⟨n, hn, hqn, hnx⟩ := hx
  obtain ⟨m, hm, hqm, hmy⟩ := hy
  refine ⟨n * m, Nat.mul_pos hn hm, fun h => (hq.dvd_mul.mp h).elim hqn hqm, ?_⟩
  rw [nsmul_add, mul_nsmul, hnx, nsmul_zero, zero_add, mul_comm n m, mul_nsmul, hmy, nsmul_zero]

theorem neg [AddCommGroup M] {x : M} (hx : PrimeToTorsion q x) : PrimeToTorsion q (-x) := by
  obtain ⟨n, hn, hqn, hnx⟩ := hx
  exact ⟨n, hn, hqn, by rw [neg_nsmul, hnx, neg_zero]⟩

theorem map [AddMonoid M] [AddMonoid M'] {F : Type*} [FunLike F M M'] [AddMonoidHomClass F M M']
    (f : F) {x : M} (hx : PrimeToTorsion q x) : PrimeToTorsion q (f x) := by
  obtain ⟨n, hn, hqn, hnx⟩ := hx
  exact ⟨n, hn, hqn, by rw [← map_nsmul, hnx, map_zero]⟩

end PrimeToTorsion


theorem mem_smulInvariants {G : Type*} [Group G] {I : Subgroup G} {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] {x : M} : x ∈ smulInvariants I M ↔ ∀ σ ∈ I, σ • x = x :=
  Iff.rfl

end Generic

section Inertia

variable (A : ValuationSubring Qbar) (M : ℕ)


variable {A M}

theorem mem_inertiaInvariants {x : JZero M} :
    x ∈ inertiaInvariants A M ↔ ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x :=
  Iff.rfl

end Inertia

section Semistable

variable (A : ValuationSubring Qbar) (N q : ℕ) (hq : q.Prime) [NeZero N]

variable [Module HeckeAlg (JZero (N * q))] [Module HeckeAlg (JZero N)]
  [Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in


end Semistable

end ModularCurve

end
