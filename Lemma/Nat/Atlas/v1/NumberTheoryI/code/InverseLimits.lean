import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.InverseLimits.Part2
open Set


/--
[InvLim.proj_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma InvLim.proj_compat
  [Preorder ι]
  {X : ι → Type*}
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
  {x : InvLim X f}
  {i j : ι}
-- given
  (h : i ≤ j) :
-- imply
  f h (x.1 j) = x.1 i :=
-- proof
  x.property h

/--
[invLim_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma invLim_isClosed
  [Preorder ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  [∀ i, T2Space (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
-- given
  (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) :
-- imply
  IsClosed (InvLim X f) := by
-- proof
  unfold InvLim
  simp_rw [setOf_forall]
  apply isClosed_iInter; intro i
  apply isClosed_iInter; intro j
  apply isClosed_iInter; intro h
  exact isClosed_eq ((hf h).comp (continuous_apply j)) (continuous_apply i)

/--
[invLim_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma invLim_isCompact
  [Preorder ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  [∀ i, T2Space (X i)]
  [∀ i, CompactSpace (X i)]
  {f : ∀ ⦃i j : ι⦄, i ≤ j → X j → X i}
-- given
  (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) :
-- imply
  IsCompact (InvLim X f) :=
-- proof
  (invLim_isClosed hf).isCompact

/--
[mem_ideal_pow_iff_evalₐ_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma mem_ideal_pow_iff_evalₐ_eq_zero (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) (x : R) :
  x ∈ (I ^ n : Ideal R) ↔
  AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) x) = 0 := by
  rw [show algebraMap R (AdicCompletion I R) x = AdicCompletion.of I R x from rfl]
  rw [AdicCompletion.evalₐ_of]
  rw [Ideal.Quotient.eq_zero_iff_mem]
section AdicCompletionTopologicalRingIso

/--
[adicComplete_ringEquiv_symm_mem_iff_evalₐ_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma adicComplete_ringEquiv_symm_mem_iff_evalₐ_eq_zero (R : Type*) [CommRing R] (I : Ideal R)
  [IsAdicComplete I R] (n : ℕ) (y : AdicCompletion I R) :
  (adicComplete_ringEquiv_adicCompletion R I).symm y ∈ (I ^ n : Ideal R) ↔
  AdicCompletion.evalₐ I n y = 0 := by
  set e := adicComplete_ringEquiv_adicCompletion R I with he
  have key : algebraMap R (AdicCompletion I R) (e.symm y) = y :=
    e.apply_symm_apply y
  constructor
  · intro h
    rw [← key,
      show algebraMap R (AdicCompletion I R) (e.symm y) =
        AdicCompletion.of I R (e.symm y) from rfl,
      AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]
    exact h
  · intro h
    rw [← key,
      show algebraMap R (AdicCompletion I R) (e.symm y) =
        AdicCompletion.of I R (e.symm y) from rfl,
      AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h

/--
[adicComplete_topological_ringIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma adicComplete_topological_ringIso
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  [IsAdicComplete I R] :
-- imply
  Nonempty (R ≃+* AdicCompletion I R) ∧ (∀ n x, x ∈ (I ^ n : Ideal R) ↔ AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) x) = 0) ∧ (∀ n y, (adicComplete_ringEquiv_adicCompletion R I).symm y ∈ (I ^ n : Ideal R) ↔ AdicCompletion.evalₐ I n y = 0) :=
-- proof
  ⟨⟨adicComplete_ringEquiv_adicCompletion R I⟩,
    fun n x => mem_ideal_pow_iff_evalₐ_eq_zero R I n x,
    fun n y => adicComplete_ringEquiv_symm_mem_iff_evalₐ_eq_zero R I n y⟩
end AdicCompletionTopologicalRingIso
variable {p : ℕ} [hp : Fact p.Prime]

/--
[padicInt_toZModPow_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma padicInt_toZModPow_injective
  {p : ℕ}
  [hp : Fact p.Prime] :
-- imply
  Function.Injective (padicIntToProd (p := p)) := by
-- proof
  intro x y h
  rw [← PadicInt.ext_of_toZModPow]
  exact fun n => congr_fun h n

/--
[padicIntToProd_compat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma padicIntToProd_compat
  {p : ℕ}
  [hp : Fact p.Prime]
  {z : ℤ_[p]}
  {m n : ℕ}
-- given
  (h : m ≤ n) :
-- imply
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (padicIntToProd z n) = padicIntToProd z m := by
-- proof
  simp only [padicIntToProd]
  exact congr_fun (congrArg DFunLike.coe
    (PadicInt.zmod_cast_comp_toZModPow m n h)) z

/--
[padicInt_toZModPow_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma padicInt_toZModPow_surjective
  {p : ℕ}
  [hp : Fact p.Prime]
-- given
  (x : ∀ n : ℕ, ZMod (p ^ n))
  (hcompat : ∀ (m n : ℕ) (h : m ≤ n), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) (x n) = x m) :
-- imply
  ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = x n := by
-- proof
  set f : ℕ → ℤ := fun n => (ZMod.val (x n) : ℤ)
  have hdvd : ∀ i, (p : ℤ) ^ i ∣ f (i + 1) - f i := by
    intro i
    haveI : NeZero (p ^ i) := ⟨pow_ne_zero i hp.out.ne_zero⟩
    haveI : NeZero (p ^ (i + 1)) := ⟨pow_ne_zero (i + 1) hp.out.ne_zero⟩
    have h := hcompat i (i + 1) (Nat.le_succ i)
    have hval : ZMod.val (x i) = ZMod.val (x (i + 1)) % p ^ i := by
      have := congr_arg ZMod.val h
      rwa [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast] at this
    simp only [f]
    rw [hval]
    have key : (ZMod.val (x (i + 1)) : ℤ) - ↑(ZMod.val (x (i + 1)) % p ^ i) =
      ↑(ZMod.val (x (i + 1)) / p ^ i) * (p : ℤ) ^ i := by
      push_cast
      have := Nat.div_add_mod (ZMod.val (x (i + 1))) (p ^ i)
      linarith
    rw [key]
    exact dvd_mul_left _ _
  set z := PadicInt.ofIntSeq f
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub f p hdvd)
  refine ⟨z, fun n => ?_⟩
  have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub f p hdvd n
  rw [this]
  simp only [f]
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  rw [Int.cast_natCast, ZMod.natCast_zmod_val]

/--
[padicIntToInvLimRingHom_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma padicIntToInvLimRingHom_bijective
  {p : ℕ}
  [hp : Fact p.Prime] :
-- imply
  Function.Bijective (padicIntToInvLimRingHom (p := p)) := by
-- proof
  constructor
  ·
    intro x y hxy
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    have := congr_arg (fun s => s.1 n) hxy
    simpa [padicIntToInvLimRingHom] using this
  ·
    intro ⟨x, hx⟩
    obtain ⟨z, hz⟩ := padicInt_toZModPow_surjective x hx
    exact ⟨z, Subtype.ext (funext hz)⟩

/--
[appr_succ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma appr_succ_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {a : ℤ_[p]}
  {n : ℕ} :
-- imply
  a.appr (n + 1) = a.appr n + p ^ n * padicDigit a n := by
-- proof
  unfold padicDigit
  have hmono : a.appr n ≤ a.appr (n + 1) := a.appr_mono (Nat.le_succ n)
  have hdvd := a.dvd_appr_sub_appr n (n + 1) (Nat.le_succ n)
  have key : a.appr (n + 1) - a.appr n = p ^ n * ((a.appr (n + 1) - a.appr n) / p ^ n) :=
    Nat.eq_mul_of_div_eq_right hdvd rfl
  omega

/--
[digitPartialSum_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma digitPartialSum_succ
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → ℕ}
  {n : ℕ} :
-- imply
  digitPartialSum p b (n + 1) = digitPartialSum p b n + p ^ n * b n :=
-- proof
  rfl

/--
[digitPartialSum_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma digitPartialSum_lt
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → ℕ}
  {n : ℕ}
-- given
  (hb : ∀ i, b i < p) :
-- imply
  digitPartialSum p b n < p ^ n := by
-- proof
  induction n with
  | zero => simp [digitPartialSum]
  | succ n ih =>
    simp only [digitPartialSum, pow_succ]
    have hbn := hb n
    have hpn_pos : 0 < p ^ n := Nat.pos_of_ne_zero (pow_ne_zero n hp.out.ne_zero)
    have hp_pos : 0 < p := hp.out.pos
    have h1 : p ^ n * b n ≤ p ^ n * (p - 1) := Nat.mul_le_mul_left _ (by omega)
    have h2 : p ^ n + p ^ n * (p - 1) = p ^ n * p := by
      have : 1 + (p - 1) = p := by omega
      nlinarith
    linarith

/--
[toZModPow_padicIntOfDigits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma toZModPow_padicIntOfDigits
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → ℕ}
  {n : ℕ}
-- given
  (hb : ∀ i, b i < p) :
-- imply
  PadicInt.toZModPow n (padicIntOfDigits b hb) = (digitPartialSum p b n : ℤ) :=
-- proof
  PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (digitPartialSum_dvd b) n

/--
[appr_padicIntOfDigits](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma appr_padicIntOfDigits
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → ℕ}
  {n : ℕ}
-- given
  (hb : ∀ i, b i < p) :
-- imply
  (padicIntOfDigits b hb).appr n = digitPartialSum p b n := by
-- proof
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  have hlt := digitPartialSum_lt b hb n
  have hzmod := toZModPow_padicIntOfDigits b hb n
  have h1 : (padicIntOfDigits b hb).appr n < p ^ n := PadicInt.appr_lt _ n
  have h2 : PadicInt.toZModPow n (padicIntOfDigits b hb) =
    ((padicIntOfDigits b hb).appr n : ZMod (p ^ n)) := by
    simp [PadicInt.toZModPow]
    rfl
  rw [h2] at hzmod
  have h3 : ((digitPartialSum p b n : ℤ) : ZMod (p ^ n)) =
    (digitPartialSum p b n : ZMod (p ^ n)) := by push_cast; ring
  rw [h3] at hzmod
  exact ZMod.val_cast_of_lt h1 ▸ ZMod.val_cast_of_lt hlt ▸
    congr_arg ZMod.val hzmod

/--
[padicExpansion_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
lemma padicExpansion_unique
  {p : ℕ}
  [hp : Fact p.Prime]
  {a a' : ℤ_[p]}
-- given
  (h : ∀ n, padicDigit a n = padicDigit a' n) :
-- imply
  a = a' := by
-- proof
  suffices happr : ∀ n, a.appr n = a'.appr n by
    rw [← PadicInt.ext_of_toZModPow]
    intro n
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have h1 : PadicInt.toZModPow n a = ((a.appr n : ℕ) : ZMod (p ^ n)) := by
      simp [PadicInt.toZModPow]; rfl
    have h2 : PadicInt.toZModPow n a' = ((a'.appr n : ℕ) : ZMod (p ^ n)) := by
      simp [PadicInt.toZModPow]; rfl
    rw [h1, h2, happr n]
  intro n
  induction n with
  | zero =>
    have h1 := a.appr_lt 0
    have h2 := a'.appr_lt 0
    simp at h1 h2
    omega
  | succ n ih =>
    rw [appr_succ_eq a n, appr_succ_eq a' n, ih, h n]

/--
[mem_ideal_pow_iff_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
private lemma mem_ideal_pow_iff_eval_eq
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  {n : ℕ}
  {x : R} :
-- imply
  x ∈ (I ^ n : Ideal R) ↔ AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) x) = 0 := by
-- proof
  apply mem_ideal_pow_iff_eval R I n x

/--
[adicComplete_ringEquiv_symm_mem_iff_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
private lemma adicComplete_ringEquiv_symm_mem_iff_eval_eq
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  [IsAdicComplete I R]
  {n : ℕ}
  {y : AdicCompletion I R} :
-- imply
  (adicComplete_ringEquiv_adicCompletion R I).symm y ∈ (I ^ n : Ideal R) ↔ AdicCompletion.evalₐ I n y = 0 := by
-- proof
  apply adicComplete_ringEquiv_symm_mem_iff_eval R I n y

/--
[digitPartialSum_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean)
-/
@[path]
private lemma digitPartialSum_dvd_eq
  {p : ℕ}
  [hp : Fact p.Prime]
  {b : ℕ → ℕ}
  {n : ℕ} :
-- imply
  (p : ℤ) ^ n ∣ (digitPartialSum p b (n + 1) : ℤ) - (digitPartialSum p b n : ℤ) := by
-- proof
  apply digitPartialSum_dvd b n


-- created on 2026-10-23
