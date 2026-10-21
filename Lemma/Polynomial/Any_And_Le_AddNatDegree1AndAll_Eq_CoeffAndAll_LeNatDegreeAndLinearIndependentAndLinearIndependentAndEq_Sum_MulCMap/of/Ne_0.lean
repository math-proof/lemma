import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_exists_tensor_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (Q : Polynomial (MvPolynomial (Fin n) ℚ))
-- given
  (hQ : Q ≠ 0) :
-- imply
  ∃ (k : ℕ) (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X]),
    0 < k ∧ k ≤ Q.natDegree + 1 ∧
      (∀ j, ∃ a ∈ Q.support, phi j = Q.coeff a) ∧
      (∀ j, (psi j).natDegree ≤ Q.natDegree) ∧
      LinearIndependent ℚ phi ∧ LinearIndependent ℚ psi ∧
      Q = ∑ j, C (phi j) * map MvPolynomial.C (psi j) := by
-- proof
  classical
  let S : Set (MvPolynomial (Fin n) ℚ) :=
    Set.range fun a : Q.support ↦ Q.coeff a
  let _ : Module.Finite ℚ (Submodule.span ℚ S) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  let k := Module.finrank ℚ (Submodule.span ℚ S)
  have hspanNontrivial : Nontrivial (Submodule.span ℚ S) := by
    obtain ⟨b, hb⟩ := support_nonempty.mpr hQ
    have hbne : Q.coeff b ≠ 0 := mem_support_iff.mp hb
    have hbmem : Q.coeff b ∈ Submodule.span ℚ S :=
      Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
    rw [nontrivial_iff]
    refine ⟨⟨Q.coeff b, hbmem⟩, 0, ?_⟩
    intro heq
    apply hbne
    exact congrArg Subtype.val heq
  have hkPos : 0 < k := Module.finrank_pos_iff.mpr hspanNontrivial
  obtain ⟨phi, hphiS, hphiSpan, hphi⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  have hcoeffSpan : ∀ a : ℕ, Q.coeff a ∈ Submodule.span ℚ (Set.range phi) := by
    intro a
    rw [hphiSpan]
    if ha : a ∈ Q.support then
      exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
    else
      rw [notMem_support_iff.mp ha]
      exact Submodule.zero_mem _
  have hcoordExists : ∀ a : ℕ, ∃ c : Fin k → ℚ,
      ∑ j, c j • phi j = Q.coeff a := by
    intro a
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hcoeffSpan a)
  choose c hc using hcoordExists
  let psi : Fin k → ℚ[X] := fun j ↦
    ∑ a ∈ Q.support, monomial a (c a j)
  have hcZero {a : ℕ} (ha : a ∉ Q.support) : ∀ j, c a j = 0 := by
    apply Fintype.linearIndependent_iff.mp hphi (c a)
    ·
      rw [hc a, notMem_support_iff.mp ha]
  have hpsiCoeff : ∀ (j : Fin k) (a : ℕ), (psi j).coeff a = c a j := by
    intro j a
    dsimp [psi]
    rw [finsetSum_coeff]
    if ha : a ∈ Q.support then
      rw [Finset.sum_eq_single a]
      ·
        simp
      ·
        intro b hb hba
        simp [coeff_monomial, hba]
      ·
        exact fun hnot ↦ (hnot ha).elim
    else
      rw [Finset.sum_eq_zero]
      ·
        exact (hcZero ha j).symm
      ·
        intro b hb
        have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
        simp [coeff_monomial, hba]
  choose a ha using hphiS
  have haCoeff : ∀ j, phi j = Q.coeff (a j) := fun j ↦ (ha j).symm
  have haInjective : Function.Injective a := by
    intro i j hij
    apply hphi.injective
    rw [haCoeff i, haCoeff j, hij]
  have hkSupport : k ≤ Q.support.card := by
    simpa using Fintype.card_le_of_injective a haInjective
  have hsupportDegree : Q.support.card ≤ Q.natDegree + 1 := by
    simpa using Finset.card_le_card supp_subset_range_natDegree_succ
  have hkDegree : k ≤ Q.natDegree + 1 := hkSupport.trans hsupportDegree
  have hcSelected : ∀ (j t : Fin k), c (a j) t = if t = j then 1 else 0 := by
    intro j
    let e : Fin k → ℚ := fun t ↦ if t = j then 1 else 0
    have heSum : ∑ t, e t • phi t = phi j := by
      simp [e]
    have hdiff : ∑ t, (c (a j) t - e t) • phi t = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib]
      rw [hc (a j), ← haCoeff j, heSum, sub_self]
    have hz := Fintype.linearIndependent_iff.mp hphi
      (fun t ↦ c (a j) t - e t) hdiff
    intro t
    exact sub_eq_zero.mp (hz t)
  have hpsi : LinearIndependent ℚ psi := by
    rw [Fintype.linearIndependent_iff]
    intro d hd j
    have hcoeff := congrArg (fun P : ℚ[X] ↦ P.coeff (a j)) hd
    have hcoeff' : ∑ t, d t * (psi t).coeff (a j) = 0 := by
      simpa using hcoeff
    have hcoeff'' : ∑ t, d t * c (a j) t = 0 := calc
      _ = ∑ t, d t * (psi t).coeff (a j) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hpsiCoeff]
      _ = 0 := hcoeff'
    simpa [hcSelected j] using hcoeff''
  have hpsiDegree : ∀ j, (psi j).natDegree ≤ Q.natDegree := by
    intro j
    rw [natDegree_le_iff_coeff_eq_zero]
    intro b hb
    rw [hpsiCoeff]
    apply hcZero
    intro hmem
    exact (not_le_of_gt hb) (le_natDegree_of_mem_supp b hmem)
  refine ⟨k, phi, psi, hkPos, hkDegree,
    fun j ↦ ⟨a j, (a j).property, haCoeff j⟩, hpsiDegree, hphi, hpsi, ?_⟩
  ·
    apply ext
    intro b
    rw [finsetSum_coeff]
    simp only [coeff_C_mul, coeff_map, hpsiCoeff]
    simpa [Algebra.smul_def, mul_comm] using (hc b).symm


-- created on 2026-10-21
