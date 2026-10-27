import Mathlib
import Initialize.Tactic.Attr.Basic
open Module


/--
[Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString.lean)
-/
@[path]
private lemma main
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {D : ℕ}
  {e : ℕ → V}
  {U : ℕ → Module.End ℂ V}
-- given
  (hD : D ≠ 0)
  (hli : LinearIndependent ℂ (fun d : Nat.divisors D => e (d : ℕ)))
  (hspan : Submodule.span ℂ (Set.range fun d : Nat.divisors D => e (d : ℕ)) = ⊤)
  (hcomm : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ D → q ∣ D → Commute (U p) (U q))
  (hdown : ∀ q : ℕ, q.Prime → q ∣ D → ∀ d : ℕ, d ∣ D → q ∣ d → U q (e d) = e (d / q))
  (hbase : ∀ q : ℕ, q.Prime → q ∣ D → ∃ a b : ℂ, ∀ d : ℕ, d ∣ D → ¬ q ∣ d →
    U q (e d) = a • e d + b • e (d * q)) :
-- imply
  (∀ d : ℕ, d ∣ D → ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
      e d = T (e D)) ∧
    ∀ lam : ℕ → ℂ,
      Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1 := by
-- proof
  classical
  have mul_dvd_of_prime_of_not_dvd {d q : ℕ} (hq : q.Prime) (hqD : q ∣ D)
    (hd : d ∣ D) (hqd : ¬ q ∣ d) : d * q ∣ D :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd).symm hd hqD
  have cyclic_part : ∀ d : ℕ, d ∣ D →
      ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
        e d = T (e D) := by
    have key : ∀ n d : ℕ, d * n = D →
        ∃ T ∈ Algebra.adjoin ℂ {A : Module.End ℂ V | ∃ q : ℕ, q.Prime ∧ q ∣ D ∧ A = U q},
          e d = T (e D) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro d hdn
        obtain rfl | hn1 := eq_or_ne n 1
        ·
          refine ⟨1, Subalgebra.one_mem _, ?_⟩
          rw [mul_one] at hdn
          rw [hdn, Module.End.one_apply]
        ·
          obtain ⟨q, hq, k, rfl⟩ := Nat.exists_prime_and_dvd hn1
          have hk0 : k ≠ 0 := by
            rintro rfl
            apply hD
            rw [← hdn, mul_zero, mul_zero]
          have hqD : q ∣ D := ⟨d * k, by rw [← hdn]; ring⟩
          have hdqD : d * q ∣ D := ⟨k, by rw [← hdn]; ring⟩
          have hk : k < q * k := by nlinarith [hq.two_le, Nat.pos_of_ne_zero hk0]
          obtain ⟨T, hT, hTe⟩ := ih k hk (d * q) (by rw [← hdn]; ring)
          refine ⟨U q * T, Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨q, hq, hqD, rfl⟩) hT, ?_⟩
          rw [Module.End.mul_apply, ← hTe, hdown q hq hqD (d * q) hdqD (dvd_mul_left q d),
            Nat.mul_div_cancel d hq.pos]
    intro d hd
    obtain ⟨n, rfl⟩ := hd
    apply key n d rfl
  have eigen_part (lam : ℕ → ℂ) :
    Module.finrank ℂ ↥(⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)) ≤ 1 := by
    let b : Basis (Nat.divisors D) ℂ V := Basis.mk hli (by rw [hspan])
    have hb : ∀ i, b i = e (i : ℕ) := fun i => Basis.mk_apply hli _ i
    have h1D : (1 : ℕ) ∈ Nat.divisors D := Nat.one_mem_divisors.mpr hD
    have key : ∀ v : V, (∀ q : ℕ, q.Prime → q ∣ D → U q v = lam q • v) →
        b.repr v ⟨1, h1D⟩ = 0 → v = 0 := by
      intro v hv h1
      suffices hall : ∀ m : ℕ, ∀ i : Nat.divisors D, (i : ℕ) = m → b.repr v i = 0 by
        apply b.repr.injective
        rw [map_zero]
        ext i
        apply hall _ i rfl
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i hi
        subst hi
        have hiD : (i : ℕ) ∣ D := Nat.dvd_of_mem_divisors i.2
        obtain hi1 | hi1 := eq_or_ne (i : ℕ) 1
        ·
          have : i = ⟨1, h1D⟩ := Subtype.ext hi1
          rw [this]
          apply h1
        ·
          obtain ⟨q, hq, m', hm'⟩ := Nat.exists_prime_and_dvd hi1
          have hqD : q ∣ D := dvd_trans (Dvd.intro m' hm'.symm) hiD
          have hm'D : m' ∣ D := dvd_trans (Dvd.intro_left q hm'.symm) hiD
          have hm'mem : m' ∈ Nat.divisors D := Nat.mem_divisors.mpr ⟨hm'D, hD⟩
          have hm'0 : 0 < m' := Nat.pos_of_mem_divisors hm'mem
          have hm'lt : m' < (i : ℕ) := by rw [hm']; nlinarith [hq.two_le]
          have hv_sum : v = ∑ j, b.repr v j • e (j : ℕ) := by
            conv_lhs => rw [← b.sum_repr v]
            simp only [hb]
          obtain ⟨a, c, habc⟩ := hbase q hq hqD
          have hcoef : b.repr (U q v) ⟨m', hm'mem⟩ = b.repr v i := calc
            _ = b.repr (U q (∑ j, b.repr v j • e (j : ℕ))) ⟨m', hm'mem⟩ := by rw [← hv_sum]
            _ = ∑ j, b.repr v j * b.repr (U q (e (j : ℕ))) ⟨m', hm'mem⟩ := by
              rw [map_sum, map_sum, Finsupp.finsetSum_apply]
              simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
            _ = b.repr v i := by
              rw [Finset.sum_eq_single i]
              ·
                rw [hdown q hq hqD i hiD (Dvd.intro m' hm'.symm)]
                have hdiv : (i : ℕ) / q = m' := by rw [hm']; apply Nat.mul_div_cancel_left m' hq.pos
                rw [hdiv, ← hb ⟨m', hm'mem⟩, b.repr_self, Finsupp.single_eq_same, mul_one]
              ·
                intro j _ hj
                have hj' : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Subtype.ext h)
                obtain hlt | hgt := lt_or_gt_of_ne hj'
                ·
                  rw [ih (j : ℕ) hlt j rfl, zero_mul]
                ·
                  have hjD : (j : ℕ) ∣ D := Nat.dvd_of_mem_divisors j.2
                  if hqj : q ∣ (j : ℕ) then
                    rw [hdown q hq hqD j hjD hqj]
                    have hjq : (j : ℕ) / q ∈ Nat.divisors D :=
                      Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd hqj) hjD, hD⟩
                    have hne : (⟨m', hm'mem⟩ : Nat.divisors D) ≠ ⟨(j : ℕ) / q, hjq⟩ := by
                      intro h
                      have h' : m' = (j : ℕ) / q := congrArg Subtype.val h
                      apply hj'
                      rw [← Nat.div_mul_cancel hqj, ← h', hm', mul_comm]
                    rw [← hb ⟨(j : ℕ) / q, hjq⟩, b.repr_self, Finsupp.single_eq_of_ne hne, mul_zero]
                  else
                    rw [habc j hjD hqj, map_add, map_smul, map_smul, Finsupp.add_apply,
                      Finsupp.smul_apply, Finsupp.smul_apply]
                    have hjqD : (j : ℕ) * q ∈ Nat.divisors D :=
                      Nat.mem_divisors.mpr ⟨mul_dvd_of_prime_of_not_dvd hq hqD hjD hqj, hD⟩
                    have hne1 : (⟨m', hm'mem⟩ : Nat.divisors D) ≠ j := by
                      intro h
                      have h' : m' = (j : ℕ) := congrArg Subtype.val h
                      omega
                    have hne2 : (⟨m', hm'mem⟩ : Nat.divisors D) ≠ ⟨(j : ℕ) * q, hjqD⟩ := by
                      intro h
                      have h' : m' = (j : ℕ) * q := congrArg Subtype.val h
                      nlinarith [hq.two_le]
                    rw [← hb j, ← hb ⟨(j : ℕ) * q, hjqD⟩, b.repr_self, b.repr_self,
                      Finsupp.single_eq_of_ne hne1, Finsupp.single_eq_of_ne hne2,
                      smul_zero, smul_zero, add_zero, mul_zero]
              ·
                intro h
                exact absurd (Finset.mem_univ i) h
          have heig : b.repr (U q v) ⟨m', hm'mem⟩ = b.repr (lam q • v) ⟨m', hm'mem⟩ := by
            rw [hv q hq hqD]
          rwa [hcoef, map_smul, Finsupp.smul_apply, smul_eq_mul, ih m' hm'lt ⟨m', hm'mem⟩ rfl,
            mul_zero] at heig
    have hf : Function.Injective ((b.coord ⟨1, h1D⟩).comp
        (⨅ q ∈ D.primeFactors, Module.End.eigenspace (U q) (lam q)).subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      apply Subtype.ext
      refine key (w : V) ?_ ?_
      ·
        intro q hq hqD
        apply Module.End.mem_eigenspace_iff.mp
          ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp w.2 q)
            (Nat.mem_primeFactors.mpr ⟨hq, hqD, hD⟩))
      ·
        simpa [Basis.coord_apply, LinearMap.comp_apply] using hw
    calc
      _ ≤ Module.finrank ℂ ℂ := LinearMap.finrank_le_finrank_of_injective hf
      _ = 1 := Module.finrank_self ℂ
  apply And.intro cyclic_part eigen_part


-- created on 2026-10-23
-- updated on 2026-10-26
