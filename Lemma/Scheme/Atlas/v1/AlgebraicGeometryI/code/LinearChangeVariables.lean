import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.LinearChangeVariables
open Cardinal Polynomial MvPolynomial NoetherNormalization Ideal Nat RingHom List Finset


/--
[Polynomial.exists_eval_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma Polynomial.exists_eval_ne_zero
  [Field k]
  [Infinite k]
  {p : Polynomial k}
-- given
  (hp : p ≠ 0) :
-- imply
  ∃ a : k, p.eval a ≠ 0 :=
-- proof
  p.exists_eval_ne_zero_of_natDegree_lt_card hp <|
    natCast_lt_aleph0.trans_le (infinite_iff.mp ‹_›)

/--
[Polynomial.exists_not_isRoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma Polynomial.exists_not_isRoot
  [Field k]
  [Infinite k]
  {p : Polynomial k}
-- given
  (hp : p ≠ 0) :
-- imply
  ∃ a : k, ¬ p.IsRoot a :=
-- proof
  Polynomial.exists_eval_ne_zero hp

/--
[Polynomial.eval_ne_zero_of_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma Polynomial.eval_ne_zero_of_infinite
  [Field k]
  [Infinite k]
  {p : Polynomial k}
-- given
  (hp : p ≠ 0) :
-- imply
  ∃ a : k, Polynomial.IsRoot p a = False := by
-- proof
  obtain ⟨a, ha⟩ := Polynomial.exists_not_isRoot hp
  exact ⟨a, eq_false ha⟩

/--
[Polynomial.eval_eval_eq_eval_map_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma Polynomial.eval_eval_eq_eval_map_eval
  [CommSemiring k]
  {p : Polynomial (Polynomial k)}
  {a b : k} :
-- imply
  (p.eval (Polynomial.C b)).eval a = (p.map (evalRingHom a)).eval b := by
-- proof
  induction p using Polynomial.induction_on' with
  | add _ _ hp hq => simp [hp, hq]
  | monomial n c =>
    simp [eval_monomial, map_monomial, eval_C, eval_pow, eval_mul]

/--
[exists_eval_ne_zero_bivariate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma exists_eval_ne_zero_bivariate
  [Field k]
  [Infinite k]
  {p : Polynomial (Polynomial k)}
-- given
  (hp : p ≠ 0) :
-- imply
  ∃ (a b : k), (p.eval (Polynomial.C b)).eval a ≠ 0 := by
-- proof
  have ⟨n, hn⟩ : ∃ n, p.coeff n ≠ 0 := by
    by_contra h; push Not at h
    exact hp (Polynomial.ext (fun n => by simp [h n]))
  obtain ⟨a, ha⟩ := Polynomial.exists_eval_ne_zero hn
  have hmap : p.map (evalRingHom a) ≠ 0 := by
    intro h
    have := congr_arg (fun q => q.coeff n) h
    simp [Polynomial.coeff_map] at this
    exact ha this
  obtain ⟨b, hb⟩ := Polynomial.exists_eval_ne_zero hmap
  exact ⟨a, b, by rwa [Polynomial.eval_eval_eq_eval_map_eval]⟩

/--
[MvPolynomial.exists_eval_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma MvPolynomial.exists_eval_ne_zero
  [Field k]
  [Infinite k]
  {f : MvPolynomial σ k}
-- given
  (hf : f ≠ 0) :
-- imply
  ∃ v : σ → k, MvPolynomial.eval v f ≠ 0 := by
-- proof
  by_contra h
  push Not at h
  exact hf (MvPolynomial.funext (fun x => by simp [h x]))
section NagataSubstitution
variable {k : Type*} [Field k] {n : ℕ}
noncomputable section
local notation3 "up" => fun (f : MvPolynomial (Fin (n + 1)) k) => 2 + f.totalDegree
local notation3 "r" => fun (f : MvPolynomial (Fin (n + 1)) k) (i : Fin (n + 1)) => (up f) ^ i.1

/--
[lt_up_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma lt_up_of_mem
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {v : Fin (n + 1) →₀ ℕ}
-- given
  (vlt : ∀ i, v i < up f) :
-- imply
  ∀ l ∈ ofFn (⇑v : Fin (n+1) → ℕ), l < up f := by
-- proof
grind

/--
[sum_r_mul_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma sum_r_mul_ne
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {v w : Fin (n + 1) →₀ ℕ}
-- given
  (vlt : ∀ i, v i < up f)
  (wlt : ∀ i, w i < up f)
  (hne : v ≠ w) :
-- imply
  ∑ x : Fin (n + 1), (r f x) * v x ≠ ∑ x : Fin (n + 1), (r f x) * w x := by
-- proof
  intro h; refine hne <| Finsupp.ext <| congrFun <| ofFn_inj.mp ?_
  apply ofDigits_inj_of_len_eq (Nat.lt_add_right f.totalDegree one_lt_two)
    (by simp) (lt_up_of_mem f v vlt) (lt_up_of_mem f w wlt)
  simpa only [ofDigits_eq_sum_mapIdx, mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, mul_comm, List.sum_ofFn] using h

/--
[degreeOf_zero_nagata](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma degreeOf_zero_nagata
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {v : Fin (n + 1) →₀ ℕ}
  {a : k}
-- given
  (ha : a ≠ 0) :
-- imply
  ((nagataEquiv f) (monomial v a)).degreeOf 0 = ∑ i : Fin (n + 1), (r f i) * v i := by
-- proof
  rw [← natDegree_finSuccEquiv, monomial_eq, Finsupp.prod_pow v fun a ↦ X a]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, map_mul, map_prod, map_pow,
    AlgEquiv.ofAlgHom_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_X, if_pos, Fin.succ_ne_zero,
    ite_false, one_smul, map_add, finSuccEquiv_X_zero, finSuccEquiv_X_succ, algebraMap_eq]
  have h (i : Fin n) :
    (Polynomial.C (X (R := k) i) + Polynomial.X ^ r f i.succ) ^ v i.succ ≠ 0 :=
    pow_ne_zero (v i.succ) (leadingCoeff_ne_zero.mp <| by simp [add_comm, leadingCoeff_X_pow_add_C])
  rw [natDegree_mul (by simp [ha]) (mul_ne_zero (by simp) (Finset.prod_ne_zero_iff.mpr
    (fun i _ ↦ h i))), natDegree_mul (by simp) (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ h i)),
    natDegree_prod _ _ (fun i _ ↦ h i), natDegree_finSuccEquiv, degreeOf_C]
  simpa only [natDegree_pow, zero_add, natDegree_X, mul_one, Fin.val_zero, pow_zero, one_mul,
    add_right_inj] using Finset.sum_congr rfl (fun i _ ↦ by
    rw [add_comm (Polynomial.C _), natDegree_X_pow_add_C, mul_comm])

/--
[degreeOf_ne_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma degreeOf_ne_of_ne
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {v w : Fin (n + 1) →₀ ℕ}
-- given
  (hv : v ∈ f.support)
  (hw : w ∈ f.support)
  (hne : v ≠ w) :
-- imply
  (nagataEquiv f <| monomial v <| coeff v f).degreeOf 0 ≠ (nagataEquiv f <| monomial w <| coeff w f).degreeOf 0 := by
-- proof
  rw [degreeOf_zero_nagata _ _ (mem_support_iff.mp hv),
    degreeOf_zero_nagata _ _ (mem_support_iff.mp hw)]
  refine sum_r_mul_ne f v w (fun i ↦ ?_) (fun i ↦ ?_) hne <;>
  exact lt_of_le_of_lt ((monomial_le_degreeOf i ‹_›).trans (degreeOf_le_totalDegree f i)) (by lia)

/--
[leadingCoeff_finSuccEquiv_nagata](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma leadingCoeff_finSuccEquiv_nagata
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {v : Fin (n + 1) →₀ ℕ} :
-- imply
  (finSuccEquiv k n ((nagataEquiv f) ((monomial v) (coeff v f)))).leadingCoeff = algebraMap k _ (coeff v f) := by
-- proof
  rw [monomial_eq, Finsupp.prod_fintype]
  · simp only [map_mul, map_prod, leadingCoeff_mul, leadingCoeff_prod]
    rw [AlgEquiv.ofAlgHom_apply, algHom_C, algebraMap_eq, finSuccEquiv_apply, eval₂Hom_C, coe_comp]
    simp only [AlgEquiv.ofAlgHom_apply, Function.comp_apply, leadingCoeff_C, map_pow,
      leadingCoeff_pow, algebraMap_eq]
    have : ∀ j, ((finSuccEquiv k n) ((T1 f) 1 (X j))).leadingCoeff = 1 := fun j ↦ by
      by_cases h : j = 0
      · simp [h, finSuccEquiv_apply]
      · simp only [aeval_eq_bind₁, bind₁_X_right, if_neg h, one_smul, map_add, map_pow]
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h
        simp [finSuccEquiv_X_succ, finSuccEquiv_X_zero, add_comm]
    simp only [this, one_pow, Finset.prod_const_one, mul_one]
  exact fun i ↦ pow_zero _

/--
[nagata_leadingcoeff_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma nagata_leadingcoeff_isUnit
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
-- given
  (fne : f ≠ 0) :
-- imply
  IsUnit (finSuccEquiv k n (nagataEquiv f f)).leadingCoeff := by
-- proof
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (nagataEquiv f ((monomial v) (coeff v f))).degreeOf 0) (support_nonempty.mpr fne)
  set h := fun w ↦ (MvPolynomial.monomial w) (coeff w f)
  simp only [← natDegree_finSuccEquiv] at vs
  replace vs : ∀ x ∈ f.support \ {v}, (finSuccEquiv k n ((nagataEquiv f) (h x))).degree <
    (finSuccEquiv k n ((nagataEquiv f) (h v))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree <| lt_of_le_of_ne (vs x h1) ?_
    simpa only [natDegree_finSuccEquiv]
      using degreeOf_ne_of_ne f _ _ h1 vin <| ne_of_not_mem_cons h2
  have hcoeff :
    (finSuccEquiv k n ((nagataEquiv f) (h v + ∑ x ∈ f.support \ {v}, h x))).leadingCoeff =
    (finSuccEquiv k n ((nagataEquiv f) (h v))).leadingCoeff := by
    simp only [map_add, map_sum]; rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : h v ≠ 0 := by simpa [h] using mem_support_iff.mp vin
    replace h2 : (finSuccEquiv k n ((nagataEquiv f) (h v))) ≠ 0 := fun eq ↦ h2 <|
      by simpa only [map_eq_zero_iff _ (AlgEquiv.injective _)] using eq
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h2 <| degree_eq_bot.mp x)).mpr vs
  nth_rw 2 [← f.support_sum_monomial_coeff]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem vin h]
  rw [leadingCoeff_finSuccEquiv_nagata] at hcoeff
  simpa only [hcoeff, algebraMap_eq] using
    (mem_support_iff.mp vin).isUnit.map (MvPolynomial.C (σ := Fin n))
end
end NagataSubstitution

/--
[MvPolynomial.exists_algEquiv_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
lemma MvPolynomial.exists_algEquiv_monic
  [Field k]
  [Infinite k]
  {n : ℕ}
  {P : MvPolynomial (Fin (n + 1)) k}
-- given
  (hP : 0 < P.totalDegree) :
-- imply
  ∃ (phi : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k), IsUnit (MvPolynomial.finSuccEquiv k n (phi P)).leadingCoeff :=
-- proof
  ⟨nagataEquiv P, nagata_leadingcoeff_isUnit P (by intro h; simp [h] at hP)⟩
/-- Lec 3, Lem 3 (linear change of variables, monic form): there is a
`k`-algebra automorphism `phi` after which `phi P` becomes monic in
`x_0` with degree equal to the total degree of `P`. -/

/--
[t1_comp_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearChangeVariables.lean)
-/
@[path]
private lemma t1_comp_neg_eq
  [Field k]
  {n : ℕ}
  {f : MvPolynomial (Fin (n + 1)) k}
  {c : k} :
-- imply
  (T1 f c).comp (T1 f (-c)) = AlgHom.id _ _ := by
-- proof
  apply t1_comp_neg f c


-- created on 2026-10-23
