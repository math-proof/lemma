import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.Dynamics.EventuallyPeriodicSequence
import Lemma.Set.EventuallyPeriodicSequence
import Lemma.Nat.ContinuedFractions.LagrangePeriodic
import Theorem.NumberTheory.ContinuedFractions.LagrangePeriodic.Part5


namespace MetaMathlibExt

/--
[isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/EulerPeriodic.lean)
-/
@[path]
lemma isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic
  {x : ℝ}
-- given
  (h : ContinuedFractionEventuallyPeriodic x) :
-- imply
  IsRealQuadraticIrrational x := by
-- proof
  obtain ⟨hTerm, hPer⟩ := h
  obtain ⟨p, n₀, hp, hper0⟩ := hPer
  have hper : ∀ n : ℕ, n₀ ≤ n →
    (GenContFract.of x).partDens.get? (n + p) = (GenContFract.of x).partDens.get? n :=
    fun n hn => hper0 n hn
  let F : ℝ → ℝ := fun y => (Int.fract y)⁻¹
  let cq : ℕ → ℝ := fun k => F^[k] x
  have hc0 : cq 0 = x := by simp [cq]
  have hcs : ∀ k, cq (k + 1) = (Int.fract (cq k))⁻¹ := by
    intro k
    simp [cq, F, Function.iterate_succ_apply']
  have hNT : ∀ k, GenContFract.IntFractPair.stream x k ≠ none := by
    intro k hk
    apply hTerm
    cases k with
    | zero => simp [GenContFract.IntFractPair.stream] at hk
    | succ k =>
      exact ⟨k, GenContFract.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr hk⟩
  have hS : ∀ m, (GenContFract.IntFractPair.stream x m =
    some ⟨⌊cq m⌋, Int.fract (cq m)⟩) ∧ (Int.fract (cq m) ≠ 0) := by
    intro m
    induction m with
    | zero =>
      have hform : GenContFract.IntFractPair.stream x 0 =
        some ⟨⌊cq 0⌋, Int.fract (cq 0)⟩ := by
        rw [hc0]
        rfl
      refine ⟨hform, ?_⟩
      intro hz
      apply hNT _
      simpa using GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hform hz
    | succ m ih =>
      obtain ⟨hform, hne⟩ := ih
      have hform' : GenContFract.IntFractPair.stream x m =
        some (GenContFract.IntFractPair.of (cq m)) := hform
      have hstep := GenContFract.IntFractPair.stream_succ_of_some hform' hne
      have hformS : GenContFract.IntFractPair.stream x (m + 1) =
        some ⟨⌊cq (m + 1)⌋, Int.fract (cq (m + 1))⟩ := by
        rwa [hcs m]
      refine ⟨hformS, ?_⟩
      intro hz
      apply hNT _
      simpa using GenContFract.IntFractPair.stream_eq_none_of_fr_eq_zero hformS hz
  have hShift : ∀ k j, GenContFract.IntFractPair.stream (cq k) j =
    GenContFract.IntFractPair.stream x (k + j) := by
    intro k j
    induction j generalizing k with
    | zero =>
      rw [Nat.add_zero]
      exact (GenContFract.IntFractPair.stream_zero (cq k)).trans (hS k).1.symm
    | succ j ih =>
      have hne : Int.fract (cq k) ≠ 0 := (hS k).2
      rw [GenContFract.IntFractPair.stream_succ hne j, ← hcs k, ih (k + 1),
        show k + 1 + j = k + (j + 1) by omega]
  have hTail : ∀ k j, (GenContFract.of (cq k)).s.get? j =
    (GenContFract.of x).s.get? (k + j) := by
    intro k j
    induction k generalizing j with
    | zero =>
      rw [hc0]
      simp
    | succ k ih =>
      have e1 : GenContFract.of (cq (k + 1)) =
        GenContFract.of ((Int.fract (cq k))⁻¹) := by rw [hcs k]
      rw [e1, ← GenContFract.of_s_tail (cq k), Stream'.Seq.get?_tail, ih (j + 1),
        show k + (j + 1) = (k + 1) + j by omega]
  have hsome : ∀ m, (GenContFract.of x).s.get? m ≠ none := by
    intro m hm
    apply hTerm
    exact ⟨m, GenContFract.terminatedAt_iff_s_none.mpr hm⟩
  have hss : ∀ n, n₀ ≤ n →
    (GenContFract.of x).s.get? (n + p) = (GenContFract.of x).s.get? n := by
    intro n hn
    obtain ⟨gp1, h1⟩ := Option.ne_none_iff_exists'.mp (hsome (n + p))
    obtain ⟨gp2, h2⟩ := Option.ne_none_iff_exists'.mp (hsome n)
    have ha1 : gp1.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a h1)
    have ha2 : gp2.a = 1 :=
      GenContFract.of_partNum_eq_one (GenContFract.partNum_eq_s_a h2)
    have hb : gp1.b = gp2.b := by
      have e : (GenContFract.of x).partDens.get? (n + p) =
        (GenContFract.of x).partDens.get? n := hper n hn
      rw [GenContFract.partDen_eq_s_b h1, GenContFract.partDen_eq_s_b h2] at e
      exact Option.some.inj e
    have hgp : gp1 = gp2 := by
      obtain ⟨a1, b1⟩ := gp1
      obtain ⟨a2, b2⟩ := gp2
      simp only at ha1 ha2 hb
      rw [ha1, ha2, hb]
    rw [h1, h2, hgp]
  obtain ⟨m, hpm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp).symm⟩
  subst hpm
  have hsform : ∀ n, (GenContFract.of x).s.get? n =
    some ⟨1, ((⌊cq (n + 1)⌋ : ℤ) : ℝ)⟩ := by
    intro n
    have hst := (hS (n + 1)).1
    have h2 := GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream hst
    simpa using h2
  have hGCF : GenContFract.of (cq (n₀ + 1)) = GenContFract.of (cq (n₀ + 1 + (m + 1))) := by
    have hh : (GenContFract.of (cq (n₀ + 1))).h =
      (GenContFract.of (cq (n₀ + 1 + (m + 1)))).h := by
      rw [GenContFract.of_h_eq_floor, GenContFract.of_h_eq_floor]
      have e := hss n₀ le_rfl
      rw [hsform n₀, hsform (n₀ + (m + 1))] at e
      have eb : ((⌊cq (n₀ + (m + 1) + 1)⌋ : ℤ) : ℝ) =
        ((⌊cq (n₀ + 1)⌋ : ℤ) : ℝ) := by
        simpa using e
      have ei : ⌊cq (n₀ + (m + 1) + 1)⌋ = ⌊cq (n₀ + 1)⌋ := by exact_mod_cast eb
      have idx : n₀ + (m + 1) + 1 = n₀ + 1 + (m + 1) := by omega
      rw [idx] at ei
      exact_mod_cast ei.symm
    have hseq : (GenContFract.of (cq (n₀ + 1))).s =
      (GenContFract.of (cq (n₀ + 1 + (m + 1)))).s := by
      apply Stream'.Seq.ext
      intro j
      rw [hTail (n₀ + 1) j, hTail (n₀ + 1 + (m + 1)) j,
        show (n₀ + 1 + (m + 1)) + j = ((n₀ + 1) + j) + (m + 1) by omega,
        hss _ (by omega)]
    exact GenContFract.ext hh hseq
  have hfix : cq (n₀ + 1) = cq (n₀ + 1 + (m + 1)) := by
    have hconvs : (GenContFract.of (cq (n₀ + 1))).convs =
      (GenContFract.of (cq (n₀ + 1 + (m + 1)))).convs := by rw [hGCF]
    have t1 := GenContFract.of_convergence (cq (n₀ + 1))
    have t2 := GenContFract.of_convergence (cq (n₀ + 1 + (m + 1)))
    rw [hconvs] at t1
    exact tendsto_nhds_unique t1 t2
  have hNTξ : ¬ (GenContFract.of (cq (n₀ + 1))).Terminates := by
    intro ht
    apply hTerm
    obtain ⟨j, hj⟩ := ht
    have hjg : (GenContFract.of (cq (n₀ + 1))).TerminatedAt j :=
      GenContFract.terminatedAt_iff_s_terminatedAt.mpr hj
    have hj' : (GenContFract.of (cq (n₀ + 1))).s.get? j = none :=
      GenContFract.terminatedAt_iff_s_none.mp hjg
    rw [hTail (n₀ + 1) j] at hj'
    exact ⟨(n₀ + 1) + j, GenContFract.terminatedAt_iff_s_none.mpr hj'⟩
  have hξm : GenContFract.IntFractPair.stream (cq (n₀ + 1)) m =
    some ⟨⌊cq ((n₀ + 1) + m)⌋, Int.fract (cq ((n₀ + 1) + m))⟩ := by
    rw [hShift (n₀ + 1) m]
    exact (hS _).1
  have hfrne : Int.fract (cq ((n₀ + 1) + m)) ≠ 0 := (hS _).2
  have hfrinv : (Int.fract (cq ((n₀ + 1) + m)))⁻¹ = cq (n₀ + 1) := by
    have e1 : ((n₀ + 1) + m) + 1 = n₀ + 1 + (m + 1) := by omega
    have e2 := hcs ((n₀ + 1) + m)
    rw [e1] at e2
    exact e2.symm.trans hfix.symm
  have hcorr := GenContFract.compExactValue_correctness_of_stream_eq_some hξm
  obtain ⟨qc', hqc'⟩ :=
    GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux (cq (n₀ + 1)) m
  obtain ⟨qc, hqc⟩ :=
    GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux (cq (n₀ + 1)) (m + 1)
  rw [hqc', hqc] at hcorr
  have hunfold : GenContFract.compExactValue (GenContFract.Pair.map Rat.cast qc')
    (GenContFract.Pair.map Rat.cast qc) (Int.fract (cq ((n₀ + 1) + m))) =
    (((Int.fract (cq ((n₀ + 1) + m)))⁻¹ * (↑(qc.a) : ℝ) + (↑(qc'.a) : ℝ)) /
      ((Int.fract (cq ((n₀ + 1) + m)))⁻¹ * (↑(qc.b) : ℝ) + (↑(qc'.b) : ℝ))) := by
    unfold GenContFract.compExactValue
    rw [ite_eq_right hfrne]
    simp [GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
      GenContFract.Pair.map]
  rw [hunfold, hfrinv] at hcorr
  have hBdens : (GenContFract.of (cq (n₀ + 1))).dens m = ↑(qc.b) := by
    rw [GenContFract.den_eq_conts_b, GenContFract.nth_cont_eq_succ_nth_contAux, hqc]
    rfl
  have hm0 : m = 0 ∨ ¬ (GenContFract.of (cq (n₀ + 1))).TerminatedAt (m - 1) := by
    obtain rfl | hne := eq_or_ne m 0
    · exact Or.inl rfl
    · exact Or.inr (fun ht => hNTξ ⟨m - 1, ht⟩)
  have hfib : ((Nat.fib (m + 1) : ℕ) : ℝ) ≤
    (GenContFract.of (cq (n₀ + 1))).dens m :=
    GenContFract.succ_nth_fib_le_of_nth_den hm0
  rw [hBdens] at hfib
  have hBone : (1 : ℝ) ≤ ↑(qc.b) := by
    have h2 : 1 ≤ Nat.fib (m + 1) := Nat.fib_pos.mpr (Nat.succ_pos m)
    have h2r : (1 : ℝ) ≤ ((Nat.fib (m + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    exact le_trans h2r hfib
  have hB'nn : (0 : ℝ) ≤ ↑(qc'.b) := by
    have h0 : (0 : ℝ) ≤ ((GenContFract.of (cq (n₀ + 1))).contsAux m).b :=
      GenContFract.zero_le_of_contsAux_b
    rwa [hqc'] at h0
  have hfr0 : 0 < Int.fract (cq n₀) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (hS n₀).2)
  have hfr1 : Int.fract (cq n₀) < 1 := Int.fract_lt_one _
  have hξ1 : 1 < cq (n₀ + 1) := by
    have e : cq (n₀ + 1) = (Int.fract (cq n₀))⁻¹ := hcs n₀
    rw [e]
    exact (one_lt_inv₀ hfr0).mpr hfr1
  have hξpos : 0 < cq (n₀ + 1) := zero_lt_one.trans hξ1
  have hBpos : 0 < (↑(qc.b) : ℝ) := zero_lt_one.trans_le hBone
  have hden : cq (n₀ + 1) * ↑(qc.b) + ↑(qc'.b) ≠ 0 := by
    have hpos : 0 < cq (n₀ + 1) * ↑(qc.b) + ↑(qc'.b) := by positivity
    exact ne_of_gt hpos
  have heq2 : cq (n₀ + 1) * (cq (n₀ + 1) * ↑(qc.b) + ↑(qc'.b)) =
    cq (n₀ + 1) * ↑(qc.a) + ↑(qc'.a) := by
    nth_rewrite 1 [hcorr]
    exact div_mul_cancel₀ _ hden
  have heq3 : (↑(qc.b) : ℝ) * (cq (n₀ + 1) ^ 2) + (↑(qc'.b) - ↑(qc.a)) * cq (n₀ + 1) -
    ↑(qc'.a) = 0 := by
    linear_combination heq2
  have hcast : ∀ q : ℚ, (algebraMap ℚ ℝ q : ℝ) = (↑q : ℝ) := fun q => rfl
  set P : Polynomial ℚ :=
    Polynomial.X ^ 2 +
      (Polynomial.C ((qc'.b - qc.a) / qc.b) * Polynomial.X +
        Polynomial.C (-qc'.a / qc.b)) with hPdef
  have hdeg1 : (Polynomial.C ((qc'.b - qc.a) / qc.b) * Polynomial.X +
    Polynomial.C (-qc'.a / qc.b) : Polynomial ℚ).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) ?_
    refine max_le_iff.mpr ⟨?_, ?_⟩
    · refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
    · rw [Polynomial.natDegree_C]
      exact Nat.zero_le 1
  have hrest_deg : (Polynomial.C ((qc'.b - qc.a) / qc.b) * Polynomial.X +
    Polynomial.C (-qc'.a / qc.b) : Polynomial ℚ).degree <
    ((2 : ℕ) : WithBot ℕ) := by
    calc (Polynomial.C ((qc'.b - qc.a) / qc.b) * Polynomial.X +
      Polynomial.C (-qc'.a / qc.b) : Polynomial ℚ).degree
      ≤ ((((Polynomial.C ((qc'.b - qc.a) / qc.b) * Polynomial.X +
        Polynomial.C (-qc'.a / qc.b) : Polynomial ℚ).natDegree : ℕ)) : WithBot ℕ) :=
        Polynomial.degree_le_natDegree
      _ ≤ ((1 : ℕ) : WithBot ℕ) := by exact_mod_cast hdeg1
      _ < ((2 : ℕ) : WithBot ℕ) := by norm_num
  have hPmonic : P.Monic := by
    rw [hPdef]
    exact Polynomial.monic_X_pow_add hrest_deg
  have hPdeg : P.degree = ((2 : ℕ) : WithBot ℕ) := by
    rw [hPdef]
    have hXdeg : (Polynomial.X ^ 2 : Polynomial ℚ).degree = ((2 : ℕ) : WithBot ℕ) := by
      rw [Polynomial.degree_X_pow]
    have hlt : (Polynomial.C ((qc'.b - qc.a) / qc.b) * Polynomial.X +
      Polynomial.C (-qc'.a / qc.b) : Polynomial ℚ).degree <
      (Polynomial.X ^ 2 : Polynomial ℚ).degree := by
      rwa [hXdeg]
    rw [Polynomial.degree_add_eq_left_of_degree_lt hlt, hXdeg]
  have hval : Polynomial.aeval (cq (n₀ + 1)) P = 0 := by
    rw [hPdef]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hcast]
    push_cast
    have hbR : (↑(qc.b) : ℝ) ≠ 0 := ne_of_gt hBpos
    field_simp [hbR]
    rw [mul_zero]
    linear_combination heq3
  have hξint : IsIntegral ℚ (cq (n₀ + 1)) := ⟨P, hPmonic, hval⟩
  have hξdeg : (minpoly ℚ (cq (n₀ + 1))).natDegree ≤ 2 := by
    have hle := minpoly.min ℚ (cq (n₀ + 1)) hPmonic hval
    rw [hPdeg] at hle
    exact Polynomial.natDegree_le_of_degree_le hle
  have hxm : GenContFract.IntFractPair.stream x n₀ =
    some ⟨⌊cq n₀⌋, Int.fract (cq n₀)⟩ := (hS n₀).1
  have hfrinvx : (Int.fract (cq n₀))⁻¹ = cq (n₀ + 1) := (hcs n₀).symm
  have hcorrx := GenContFract.compExactValue_correctness_of_stream_eq_some hxm
  obtain ⟨qd', hqd'⟩ := GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux x n₀
  obtain ⟨qd, hqd⟩ := GenContFract.exists_gcf_pair_rat_eq_of_nth_contsAux x (n₀ + 1)
  rw [hqd', hqd] at hcorrx
  have hunfoldx : GenContFract.compExactValue (GenContFract.Pair.map Rat.cast qd')
    (GenContFract.Pair.map Rat.cast qd) (Int.fract (cq n₀)) =
    (((Int.fract (cq n₀))⁻¹ * (↑(qd.a) : ℝ) + (↑(qd'.a) : ℝ)) /
      ((Int.fract (cq n₀))⁻¹ * (↑(qd.b) : ℝ) + (↑(qd'.b) : ℝ))) := by
    unfold GenContFract.compExactValue
    rw [ite_eq_right (hS n₀).2]
    simp [GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen,
      GenContFract.Pair.map]
  rw [hunfoldx, hfrinvx] at hcorrx
  have hmem : ∀ q : ℚ, ((↑q : ℝ)) ∈ IntermediateField.adjoin ℚ {cq (n₀ + 1)} := by
    intro q
    have h0 : (algebraMap ℚ ℝ q : ℝ) ∈ IntermediateField.adjoin ℚ {cq (n₀ + 1)} :=
      IntermediateField.algebraMap_mem _ q
    rwa [hcast q] at h0
  have hxK : x ∈ IntermediateField.adjoin ℚ {cq (n₀ + 1)} := by
    rw [hcorrx]
    apply IntermediateField.div_mem
    · apply IntermediateField.add_mem
      · apply IntermediateField.mul_mem
        · exact IntermediateField.mem_adjoin_simple_self ℚ _
        · exact hmem _
      · exact hmem _
    · apply IntermediateField.add_mem
      · apply IntermediateField.mul_mem
        · exact IntermediateField.mem_adjoin_simple_self ℚ _
        · exact hmem _
      · exact hmem _
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {cq (n₀ + 1)}) :=
    IntermediateField.adjoin.finiteDimensional hξint
  have := hfin
  have hle : (minpoly ℚ (⟨x, hxK⟩ : IntermediateField.adjoin ℚ {cq (n₀ + 1)})).natDegree ≤
    Module.finrank ℚ (IntermediateField.adjoin ℚ {cq (n₀ + 1)}) :=
    minpoly.natDegree_le _
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {cq (n₀ + 1)}) =
    (minpoly ℚ (cq (n₀ + 1))).natDegree :=
    IntermediateField.adjoin.finrank hξint
  have hmin_eq : minpoly ℚ (⟨x, hxK⟩ : IntermediateField.adjoin ℚ {cq (n₀ + 1)}) =
    minpoly ℚ x :=
    IntermediateField.minpoly_eq _
  have hdegx : (minpoly ℚ x).natDegree ≤ 2 := by
    have h1 := hle
    rw [hmin_eq, hfr] at h1
    omega
  have hInt : IsIntegral ℚ x := by
    rw [← minpoly.ne_zero_iff]
    rw [← hmin_eq]
    exact Polynomial.Monic.ne_zero (minpoly.monic (IsIntegral.of_finite ℚ _))
  have hirr : x ∉ (algebraMap ℚ ℝ).range := by
    rintro ⟨q, hq⟩
    have hcastq : (algebraMap ℚ ℝ q : ℝ) = (↑q : ℝ) := rfl
    rw [hcastq] at hq
    apply hTerm
    exact (GenContFract.terminates_iff_rat x).mpr ⟨q, hq.symm⟩
  have hne1 : (minpoly ℚ x).natDegree ≠ 1 := by
    intro h1
    apply hirr
    exact minpoly.natDegree_eq_one_iff.mp h1
  have hpos : 0 < (minpoly ℚ x).natDegree := minpoly.natDegree_pos hInt
  exact ⟨hInt, by omega⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/EulerPeriodic.lean)
-/
@[path]
lemma continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational
  {x : ℝ} :
-- imply
  ContinuedFractionEventuallyPeriodic x ↔ IsRealQuadraticIrrational x :=
-- proof
  ⟨isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic x,
    continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational x⟩
end



-- created on 2026-10-20
-- updated on 2026-10-26
