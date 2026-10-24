import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_pow_pow_eq
  (p : ℕ) [Fact p.Prime]
  {E : Type} [CommRing E] [Algebra (ZMod p) E] [Module.Finite (ZMod p) E] [IsReduced E] [Nontrivial E] :
  -- imply
  ∃ R : ℕ, 0 < R ∧ ∀ y : E, y ^ p ^ R = y := by
  -- proof
  let _ : CharP E p := charP_of_injective_algebraMap (algebraMap (ZMod p) E).injective p
  let _ : Finite E := Module.finite_of_finite (ZMod p)
  have hinj : Function.Injective (frobenius E p) := frobenius_inj E p
  have hbij : Function.Bijective (frobenius E p) := Iff.mp Finite.injective_iff_bijective hinj
  let σ : Equiv.Perm E := Equiv.ofBijective _ hbij
  refine ⟨orderOf σ, orderOf_pos σ, fun y => ?_⟩
  have h1 : (σ ^ orderOf σ) y = y := by
    rw [pow_orderOf_eq_one]
    rfl
  have h2 : ∀ n : ℕ, (σ ^ n) y = y ^ p ^ n := by
    intro n
    induction n
    · simp
    ·
      rename_i n ih
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      show (frobenius E p) (y ^ p ^ n) = _
      rw [frobenius_def, ← pow_mul, ← pow_succ]
  rw [← h2, h1]

private lemma eq_zero_of_pow_eq_of_isNilpotent
  {A : Type} [CommRing A]
  {n : A} {q : ℕ}
  -- given
  (hn : IsNilpotent n)
  (hq : 2 ≤ q)
  (h : n ^ q = n) :
  -- imply
  n = 0 := by
  -- proof
  obtain ⟨m, hm⟩ := hn
  have hiter : ∀ k : ℕ, n ^ q ^ k = n := by
    intro k
    induction k
    · simp
    ·
      rename_i k ih
      rw [pow_succ, pow_mul, ih, h]
  have hle : m ≤ q ^ m := calc
    _ ≤ 2 ^ m := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ q ^ m := Nat.pow_le_pow_left hq m
  have : n ^ q ^ m = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    rw [hd, pow_add, hm, zero_mul]
  rw [← hiter m, this]

private lemma bialgHom_eq_counit
  (p : ℕ) [Fact p.Prime]
  (Ge : Type) [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
  (Gc : Type) [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
  (φ : BialgHom (ZMod p) Ge Gc)
  (y : Ge)
  -- given
  (hGc : IsLocalRing Gc)
  (hGe : IsReduced Ge) :
  -- imply
  φ y = algebraMap (ZMod p) Gc (Coalgebra.counit (R := ZMod p) y) := by
  -- proof
  let _ : IsLocalRing Gc := hGc
  let _ : IsReduced Ge := hGe
  let _ : Nontrivial Ge := (Bialgebra.counitAlgHom (ZMod p) Ge : Ge →+* ZMod p).domain_nontrivial
  let _ : Nontrivial Gc := (Bialgebra.counitAlgHom (ZMod p) Gc : Gc →+* ZMod p).domain_nontrivial
  let _ : CharP Gc p := charP_of_injective_algebraMap (algebraMap (ZMod p) Gc).injective p
  let _ : IsArtinianRing Gc := isArtinian_of_tower (ZMod p) inferInstance
  have hzmod : ∀ (k : ℕ) (a : ZMod p), a ^ p ^ k = a := by
    intro k
    induction k
    ·
      intro a
      simp
    ·
      rename_i k ih
      intro a
      rw [pow_succ, pow_mul, ih, ZMod.pow_card]
  obtain ⟨R, hR, hfix⟩ := exists_pow_pow_eq p (E := Ge)
  set z := φ y with hz
  set c := algebraMap (ZMod p) Gc (Coalgebra.counit (R := ZMod p) z) with hc
  set n := z - c with hn
  have hnm : n ∈ IsLocalRing.maximalIdeal Gc := by
    apply IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (Bialgebra.counitAlgHom (ZMod p) Gc : Gc →+* ZMod p))
    rw [RingHom.mem_ker, hn, map_sub]
    show Coalgebra.counit (R := ZMod p) z - Bialgebra.counitAlgHom (ZMod p) Gc (algebraMap (ZMod p) Gc _) = 0
    rw [AlgHom.commutes]
    apply sub_self
  have hnil : IsNilpotent n := by
    have hJ : IsNilpotent (IsLocalRing.maximalIdeal Gc) := by
      rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      apply IsArtinianRing.isNilpotent_jacobson_bot
    obtain ⟨m, hm⟩ := hJ
    refine ⟨m, ?_⟩
    have : n ^ m ∈ (IsLocalRing.maximalIdeal Gc) ^ m := Ideal.pow_mem_pow hnm m
    rw [hm] at this
    apply Iff.mp Ideal.mem_bot this
  have hzq : z ^ p ^ R = z := by
    rw [hz, ← map_pow, hfix]
  have hcq : c ^ p ^ R = c := by
    rw [hc, ← map_pow, hzmod]
  have hnq : n ^ p ^ R = n := by
    rw [hn, sub_pow_char_pow, hzq, hcq]
  have hn0 : n = 0 := by
    refine eq_zero_of_pow_eq_of_isNilpotent hnil ?_ hnq
    calc
      _ ≤ p := (Fact.out : p.Prime).two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ R := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hR
  have hzc : z = c := by
    rw [← sub_eq_zero, ← hn, hn0]
  rw [hzc, hc, hz]
  congr 1
  apply CoalgHomClass.counit_comp_apply φ y

/--
[HopfAlgebra_existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
  {Gc : Type} [CommRing Gc] [HopfAlgebra (ZMod p) Gc] [Coalgebra.IsCocomm (ZMod p) Gc] [Module.Finite (ZMod p) Gc]
  {Ge : Type} [CommRing Ge] [HopfAlgebra (ZMod p) Ge] [Coalgebra.IsCocomm (ZMod p) Ge] [Module.Finite (ZMod p) Ge]
  (qc : BialgHom (ZMod p) B Gc)
  (σ : BialgHom (ZMod p) Ge B)
  (g : BialgHom (ZMod p) B B)
  -- given
  (hGc : IsLocalRing Gc)
  (hGe : IsReduced Ge)
  (hqc : Function.Surjective qc)
  (hkerqc : RingHom.ker (qc : B →ₐ[ZMod p] Gc) =
    Ideal.map (σ : Ge →ₐ[ZMod p] B) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) Ge))) :
  -- imply
  ∃! gc : BialgHom (ZMod p) Gc Gc, gc.comp qc = qc.comp g := by
  -- proof
  classical
  let _ : IsLocalRing Gc := hGc
  have hgI : RingHom.ker (qc : B →ₐ[ZMod p] Gc) ≤ (RingHom.ker (qc : B →ₐ[ZMod p] Gc)).comap (g : B →ₐ[ZMod p] B) := by
    rw [hkerqc, Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hkerqc, RingHom.mem_ker]
    show qc (g (σ y)) = 0
    have := bialgHom_eq_counit p Ge Gc (qc.comp (g.comp σ)) y hGc hGe
    rw [BialgHom.comp_apply, BialgHom.comp_apply] at this
    rw [this]
    have hy0 : Coalgebra.counit (R := ZMod p) y = 0 := hy
    rw [hy0, map_zero]
  have hvan : ∀ x ∈ RingHom.ker (qc : B →ₐ[ZMod p] Gc), ((qc : B →ₐ[ZMod p] Gc).comp (g : B →ₐ[ZMod p] B)) x = 0 := by
    intro x hx
    have := hgI hx
    rwa [Ideal.mem_comap, RingHom.mem_ker] at this
  let e : (B ⧸ RingHom.ker (qc : B →ₐ[ZMod p] Gc)) ≃ₐ[ZMod p] Gc := Ideal.quotientKerAlgEquivOfSurjective hqc
  have he : ∀ b : B, e (Ideal.Quotient.mk _ b) = qc b := fun b => rfl
  let ga : Gc →ₐ[ZMod p] Gc :=
    (Ideal.Quotient.liftₐ (RingHom.ker (qc : B →ₐ[ZMod p] Gc)) ((qc : B →ₐ[ZMod p] Gc).comp (g : B →ₐ[ZMod p] B)) hvan).comp
      (e.symm : Gc →ₐ[ZMod p] B ⧸ RingHom.ker (qc : B →ₐ[ZMod p] Gc))
  have hga : ∀ b : B, ga (qc b) = qc (g b) := by
    intro b
    have h1 : e.symm (qc b) = Ideal.Quotient.mk _ b := by
      rw [← he, AlgEquiv.symm_apply_apply]
    show (Ideal.Quotient.liftₐ (RingHom.ker (qc : B →ₐ[ZMod p] Gc)) ((qc : B →ₐ[ZMod p] Gc).comp (g : B →ₐ[ZMod p] B)) hvan) (e.symm (qc b)) = qc (g b)
    rw [h1]
    rfl
  have hext : ∀ {T : Type} [CommRing T] [Algebra (ZMod p) T] (f f' : Gc →ₐ[ZMod p] T), (∀ b : B, f (qc b) = f' (qc b)) → f = f' := by
    intro T _ _ f f' hff'
    apply AlgHom.ext
    intro z
    obtain ⟨b, rfl⟩ := hqc z
    apply hff' b
  have hqΔ : ∀ x : B, Bialgebra.comulAlgHom (ZMod p) Gc (qc x) =
      Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (qc : B →ₐ[ZMod p] Gc) (Bialgebra.comulAlgHom (ZMod p) B x) := by
    intro x
    apply (DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom qc) x).symm
  have hgΔ : ∀ x : B, Bialgebra.comulAlgHom (ZMod p) B (g x) =
      Algebra.TensorProduct.map (g : B →ₐ[ZMod p] B) (g : B →ₐ[ZMod p] B) (Bialgebra.comulAlgHom (ZMod p) B x) := by
    intro x
    apply (DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom g) x).symm
  have hcounit : (Bialgebra.counitAlgHom (ZMod p) Gc).comp ga = Bialgebra.counitAlgHom (ZMod p) Gc := by
    refine hext _ _ fun b => ?_
    rw [AlgHom.comp_apply, hga]
    show Coalgebra.counit (R := ZMod p) (qc (g b)) = Coalgebra.counit (R := ZMod p) (qc b)
    rw [CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  have hcomul : (Algebra.TensorProduct.map ga ga).comp (Bialgebra.comulAlgHom (ZMod p) Gc) =
      (Bialgebra.comulAlgHom (ZMod p) Gc).comp ga := by
    refine hext _ _ fun b => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hga, hqΔ, hqΔ, hgΔ,
      ← AlgHom.comp_apply (Algebra.TensorProduct.map ga ga), ← Algebra.TensorProduct.map_comp,
      ← AlgHom.comp_apply (Algebra.TensorProduct.map (qc : B →ₐ[ZMod p] Gc) (qc : B →ₐ[ZMod p] Gc)),
      ← Algebra.TensorProduct.map_comp]
    congr 2 <;> apply AlgHom.ext hga
  let gc : BialgHom (ZMod p) Gc Gc := BialgHom.ofAlgHom ga hcounit hcomul
  refine ⟨gc, ?_, ?_⟩
  ·
    apply BialgHom.coe_toAlgHom_injective
    apply AlgHom.ext hga
  ·
    intro gc' hgc'
    apply BialgHom.coe_toAlgHom_injective
    refine hext _ _ fun b => ?_
    have := DFunLike.congr_fun hgc' b
    simp only [BialgHom.comp_apply] at this
    rw [show ((gc : BialgHom (ZMod p) Gc Gc) : Gc →ₐ[ZMod p] Gc) (qc b) = qc (g b) from hga b]
    apply this


-- created on 2026-10-20
