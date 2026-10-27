import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial
open scoped TensorProduct


private abbrev lsIdeal
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) :
  Ideal (S ⊗[R] A) :=
  Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}

private noncomputable def fwd
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S] :
  S ⊗[R] A →ₐ[S] S ⊗[R[X]] A :=
  AlgHom.liftEquiv R S A (S ⊗[R[X]] A)
    ((Algebra.TensorProduct.includeRight (R := R[X]) (A := S) (B := A)).restrictScalars R)

private lemma fwd_tmul
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (x : S) (a : A) :
-- imply
  fwd R A S (x ⊗ₜ[R] a) = x ⊗ₜ[R[X]] a := by
-- proof
  rw [fwd, AlgHom.liftEquiv_tmul, AlgHom.restrictScalars_apply,
    Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private lemma fwd_rel
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s) :
-- imply
  fwd R A S ((1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)) = 0 := by
-- proof
  rw [map_sub, fwd_tmul, fwd_tmul, ← hf, ← hs, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, sub_self]

private noncomputable def fwdQ
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s) :
  (S ⊗[R] A ⧸ lsIdeal R A S f s) →ₐ[S] S ⊗[R[X]] A :=
  Ideal.Quotient.liftₐ (lsIdeal R A S f s) (fwd R A S) (by intro a ha; rw [← RingHom.mem_ker]; refine (Ideal.span_le.mpr ?_) ha; intro _ h; obtain rfl := h; apply fwd_rel R A S f s hf hs)

private lemma fwdQ_mk
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s)
  (t : S ⊗[R] A) :
-- imply
  fwdQ R A S f s hf hs (Ideal.Quotient.mk _ t) = fwd R A S t :=
  rfl

private noncomputable def bwdA₀
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) :
  A →ₐ[R] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  (Ideal.Quotient.mkₐ R (lsIdeal R A S f s)).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A))

private lemma bwdA₀_apply
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (a : A) :
-- imply
  bwdA₀ R A S f s a = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] a) :=
  rfl

private lemma bwdA₀_comp
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s) :
-- imply
  (bwdA₀ R A S f s).comp (IsScalarTower.toAlgHom R R[X] A) =
    IsScalarTower.toAlgHom R R[X] (S ⊗[R] A ⧸ lsIdeal R A S f s) := by
-- proof
  refine Polynomial.algHom_ext ?_
  simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', bwdA₀_apply, hf]
  rw [IsScalarTower.algebraMap_apply R[X] (S ⊗[R] A) (S ⊗[R] A ⧸ lsIdeal R A S f s),
    Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply, hs,
    Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

private noncomputable def bwdA
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s) :
  A →ₐ[R[X]] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  AlgHom.mk (bwdA₀ R A S f s).toRingHom (fun p => by
    have := congrArg (fun φ : R[X] →ₐ[R] _ => φ p) (bwdA₀_comp R A S f s hf hs)
    simpa using this)

private lemma bwdA_apply
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s)
  (a : A) :
-- imply
  bwdA R A S f s hf hs a = Ideal.Quotient.mk _ ((1 : S) ⊗ₜ[R] a) :=
  rfl

private noncomputable def bwd
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s) :
  S ⊗[R[X]] A →ₐ[S] (S ⊗[R] A ⧸ lsIdeal R A S f s) :=
  AlgHom.liftEquiv R[X] S A _ (bwdA R A S f s hf hs)

private lemma bwd_tmul
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s)
  (x : S) (a : A) :
-- imply
  bwd R A S f s hf hs (x ⊗ₜ[R[X]] a) = Ideal.Quotient.mk _ (x ⊗ₜ[R] a) := by
-- proof
  rw [bwd, AlgHom.liftEquiv_tmul, bwdA_apply]
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply S (S ⊗[R] A) (S ⊗[R] A ⧸ lsIdeal R A S f s),
    Ideal.Quotient.algebraMap_eq, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rfl

private noncomputable def levelSetEquiv
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s) :
  (S ⊗[R] A ⧸ lsIdeal R A S f s) ≃ₐ[S] S ⊗[R[X]] A :=
  AlgEquiv.ofAlgHom (fwdQ R A S f s hf hs) (bwd R A S f s hf hs)
    (by refine Algebra.TensorProduct.ext' fun x a => ?_; rw [AlgHom.comp_apply, bwd_tmul, fwdQ_mk, fwd_tmul, AlgHom.id_apply])
    (by refine Ideal.Quotient.algHom_ext _ (Algebra.TensorProduct.ext' fun x a => ?_); rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, fwdQ_mk, fwd_tmul, bwd_tmul, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply])

private lemma level_main
  (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  (f : A) (d : ℕ)
-- given
  (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
  (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
  (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
    Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d)
  (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S]
  (s : S) :
-- imply
  Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
    Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
    Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d := by
-- proof
  let _ : Algebra R[X] A := (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.toAlgebra
  have : IsScalarTower R R[X] A := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R A r = (Polynomial.aeval f : R[X] →ₐ[R] A) (algebraMap R R[X] r)
    rw [AlgHom.commutes]
  have : Module.Finite R[X] A := hfin
  have : Module.Flat R[X] A := hflat
  have hf : algebraMap R[X] A X = f := by
    show (Polynomial.aeval f : R[X] →ₐ[R] A) X = f
    apply Polynomial.aeval_X
  let _ : Algebra R[X] S := (Polynomial.aeval s : R[X] →ₐ[R] S).toRingHom.toAlgebra
  have : IsScalarTower R R[X] S := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R S r = (Polynomial.aeval s : R[X] →ₐ[R] S) (algebraMap R R[X] r)
    rw [AlgHom.commutes]
  have hs : algebraMap R[X] S X = s := by
    show (Polynomial.aeval s : R[X] →ₐ[R] S) X = s
    apply Polynomial.aeval_X
  let e : (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ≃ₗ[S] S ⊗[R[X]] A :=
    (levelSetEquiv R A S f s hf hs).toLinearEquiv
  have hfinS : Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
    Module.Finite.equiv e.symm
  have : Module.Flat S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
    Module.Flat.of_linearEquiv e
  have hfree : Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) :=
    Module.free_of_flat_of_isLocalRing
  refine ⟨hfinS, hfree, ?_⟩
  let κ := IsLocalRing.ResidueField S
  have hsκ : algebraMap R[X] κ X = IsLocalRing.residue S s := by
    rw [IsScalarTower.algebraMap_apply R[X] S κ, hs]
    rfl
  have h1 : Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) =
      Module.finrank S (S ⊗[R[X]] A) := e.finrank_eq
  have : Module.Free S (S ⊗[R[X]] A) := Module.Free.of_equiv e
  have h2 : Module.finrank S (S ⊗[R[X]] A) = Module.finrank κ (κ ⊗[S] (S ⊗[R[X]] A)) :=
    (Module.finrank_baseChange (R := κ) (S := S) (M' := S ⊗[R[X]] A)).symm
  have h3 : Module.finrank κ (κ ⊗[S] (S ⊗[R[X]] A)) = Module.finrank κ (κ ⊗[R[X]] A) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R[X] S κ κ A).finrank_eq
  have h4 : Module.finrank κ (κ ⊗[R[X]] A) =
      Module.finrank κ (κ ⊗[R] A ⧸ Ideal.span {(1 : κ) ⊗ₜ[R] f - (IsLocalRing.residue S s) ⊗ₜ[R] (1 : A)}) :=
    (levelSetEquiv R A κ f (IsLocalRing.residue S s) hf hsκ).toLinearEquiv.finrank_eq.symm
  rw [h1, h2, h3, h4]
  apply hrank κ (IsLocalRing.residue S s)


/--
[Algebra_levelSet_finite_free_finrank_of_flat_polynomial](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type u} [CommRing A] [Algebra R A]
  {f : A} {d : ℕ}
-- given
  (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
  (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
  (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
    Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d) :
-- imply
  ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
    Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
      Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
      Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d :=
  fun S _ _ _ s => level_main R A f d hfin hflat hrank S s


-- created on 2026-10-13
