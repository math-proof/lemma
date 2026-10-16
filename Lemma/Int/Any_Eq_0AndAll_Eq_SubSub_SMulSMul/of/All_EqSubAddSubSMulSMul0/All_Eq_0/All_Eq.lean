import Mathlib
import sympy.Basic


private def Cocycle
  (R : Type u) [CommRing R]
  (S : Type v) [CommRing S] [Algebra R S]
  (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :=
  Subtype fun (ψ : S →ₗ[R] S →ₗ[R] M) =>
    (∀ x y, ψ x y = ψ y x) ∧
    (∀ y, ψ 1 y = 0) ∧
    (∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0)

private abbrev HochExt
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (_ : Cocycle R S M) :=
  S × M

private def Cocycle.ψ
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (c : Cocycle R S M) : S →ₗ[R] S →ₗ[R] M :=
  c.1

private lemma Cocycle.symm
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (c : Cocycle R S M) (x y : S) : c.ψ x y = c.ψ y x :=
  c.2.1 x y

private lemma Cocycle.one
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (c : Cocycle R S M) : ∀ y, c.ψ 1 y = 0 :=
  c.2.2.1

private lemma Cocycle.coc
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (c : Cocycle R S M) (x y z : S) :
  x • c.ψ y z - c.ψ (x * y) z + c.ψ x (y * z) - z • c.ψ x y = 0 :=
  c.2.2.2 x y z

private lemma fst_add
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a b : HochExt c) : (a + b).fst = a.fst + b.fst := rfl

private lemma snd_add
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a b : HochExt c) : (a + b).snd = a.snd + b.snd := rfl

private lemma fst_zero
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} : (0 : HochExt c).fst = 0 := rfl

private lemma snd_zero
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} : (0 : HochExt c).snd = 0 := rfl

private lemma fst_neg
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a : HochExt c) : (-a).fst = -a.fst := rfl

private lemma snd_neg
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a : HochExt c) : (-a).snd = -a.snd := rfl

private lemma fst_smul
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (r : R) (a : HochExt c) : (r • a).fst = r • a.fst := rfl

private lemma snd_smul
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (r : R) (a : HochExt c) : (r • a).snd = r • a.snd := rfl

private instance {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] {c : Cocycle R S M} : Mul (HochExt c) :=
  ⟨fun a b => ⟨a.fst * b.fst, a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst⟩⟩

private instance {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] {c : Cocycle R S M} : One (HochExt c) :=
  ⟨⟨1, 0⟩⟩

private lemma fst_mul
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a b : HochExt c) : (a * b).fst = a.fst * b.fst := rfl

private lemma snd_mul
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a b : HochExt c) :
  (a * b).snd = a.fst • b.snd + b.fst • a.snd + c.ψ a.fst b.fst := rfl

private lemma fst_one
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} : (1 : HochExt c).fst = 1 := rfl

private lemma snd_one
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} : (1 : HochExt c).snd = 0 := rfl

private lemma hochMulComm
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a b : HochExt c) : a * b = b * a := by
  ext
  · simp only [fst_mul, mul_comm]
  ·
    simp only [snd_mul, c.symm a.fst b.fst]
    abel

private lemma mul_assoc'
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a b d : HochExt c) : a * b * d = a * (b * d) := by
  ext
  · simp only [fst_mul, mul_assoc]
  ·
    simp only [snd_mul, fst_mul, smul_add]
    rw [← sub_eq_zero]
    have h := c.coc a.fst b.fst d.fst
    calc
      _ = -(a.fst • c.ψ b.fst d.fst - c.ψ (a.fst * b.fst) d.fst +
          c.ψ a.fst (b.fst * d.fst) - d.fst • c.ψ a.fst b.fst) := by
        simp only [smul_smul]
        module
      _ = 0 := by rw [h, neg_zero]

private lemma one_mul'
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (a : HochExt c) : 1 * a = a := by
  ext
  · simp only [fst_mul, fst_one, one_mul]
  · simp only [snd_mul, fst_one, snd_one, one_smul, smul_zero, add_zero, c.one]

private instance {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] {c : Cocycle R S M} : CommRing (HochExt c) where
  __ := (inferInstance : AddCommGroup (HochExt c))
  mul := (· * ·)
  one := 1
  mul_assoc := by
    intro a b d
    apply mul_assoc'
  one_mul := by
    intro a
    apply one_mul'
  mul_one := by
    intro a
    rw [hochMulComm]
    apply one_mul'
  zero_mul := by
    intro a
    ext
    · simp only [fst_mul, fst_zero, zero_mul]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero, LinearMap.zero_apply, add_zero]
  mul_zero := by
    intro a
    ext
    · simp only [fst_mul, fst_zero, mul_zero]
    · simp only [snd_mul, fst_zero, snd_zero, zero_smul, smul_zero, map_zero, add_zero]
  left_distrib := by
    intro a b d
    ext
    · simp only [fst_mul, fst_add, mul_add]
    ·
      simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add]
      abel
  right_distrib := by
    intro a b d
    ext
    · simp only [fst_mul, fst_add, add_mul]
    ·
      simp only [snd_mul, fst_add, snd_add, smul_add, add_smul, map_add, LinearMap.add_apply]
      abel
  mul_comm := by
    intro a b
    apply hochMulComm

private lemma smul_mul_assoc'
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} (r : R) (a b : HochExt c) : (r • a) * b = r • (a * b) := by
  ext
  · simp only [fst_mul, fst_smul, smul_mul_assoc]
  ·
    simp only [snd_mul, fst_smul, snd_smul, smul_add, LinearMap.map_smul₂, smul_assoc]
    rw [smul_comm b.fst r a.snd]

private instance {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] {c : Cocycle R S M} : Algebra R (HochExt c) :=
  Algebra.ofModule smul_mul_assoc' fun r a b => by
    rw [hochMulComm, smul_mul_assoc', hochMulComm]

private def fstHom
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} : HochExt c →ₐ[R] S where
  toFun := Prod.fst
  map_one' := by rfl
  map_mul' := by
    intro _ _
    rfl
  map_zero' := by rfl
  map_add' := by
    intro _ _
    rfl
  commutes' := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one, fst_smul, fst_one, Algebra.algebraMap_eq_smul_one]

private lemma fst_eq_zero_of_mem_ker
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} {a : HochExt c}
-- given
  (ha : a ∈ RingHom.ker (fstHom (c := c) : HochExt c →+* S)) :
-- imply
  a.fst = 0 := ha

private lemma ker_sq_eq_bot
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} :
-- imply
  RingHom.ker (fstHom (c := c) : HochExt c →+* S) ^ 2 = ⊥ := by
-- proof
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  rw [Ideal.mem_bot]
  have ha' := fst_eq_zero_of_mem_ker ha
  have hb' := fst_eq_zero_of_mem_ker hb
  ext
  · simp only [fst_mul, ha', zero_mul, fst_zero]
  · simp only [snd_mul, ha', hb', zero_smul, map_zero, add_zero, snd_zero]

private lemma isNilpotent_ker
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} :
-- imply
  IsNilpotent (RingHom.ker (fstHom (c := c) : HochExt c →+* S)) := by
-- proof
  refine ⟨2, ker_sq_eq_bot⟩

private lemma fstHom_surjective
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} :
-- imply
  Function.Surjective (fstHom (c := c) : HochExt c →ₐ[R] S) := by
-- proof
  intro x
  refine ⟨⟨x, 0⟩, rfl⟩

private noncomputable def sect
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (c : Cocycle R S M) : S →ₐ[R] HochExt c :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R S) (fstHom (c := c))
    (fstHom_surjective (c := c)) (isNilpotent_ker (c := c))

private lemma fst_sect
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} {x : S} :
-- imply
  (sect c x).fst = x := by
-- proof
  apply Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R S) (fstHom (c := c))
    (fstHom_surjective (c := c)) (isNilpotent_ker (c := c)) x

private noncomputable def ell
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (c : Cocycle R S M) : S →ₗ[R] M where
  toFun x := (sect c x).snd
  map_add' := by
    intro x y
    rw [map_add, snd_add]
  map_smul' := by
    intro r x
    rw [map_smul, snd_smul, RingHom.id_apply]

private lemma ell_one
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} :
-- imply
  ell c 1 = 0 := by
-- proof
  show (sect c 1).snd = 0
  rw [map_one, snd_one]

private lemma ψ_eq
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {c : Cocycle R S M} {x y : S} :
-- imply
  c.ψ x y = ell c (x * y) - x • ell c y - y • ell c x := by
-- proof
  have h := congrArg Prod.snd (map_mul (sect c) x y)
  rw [snd_mul, fst_sect, fst_sect] at h
  change c.ψ x y = (sect c (x * y)).snd - x • (sect c y).snd - y • (sect c x).snd
  rw [h]
  abel


/--
[Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallySmooth_exists_linearMap_eq_of_symmetric_hochschild_two_cocycle.lean)
-/
@[path]
private lemma main
  {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallySmooth R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  {ψ : S →ₗ[R] S →ₗ[R] M}
-- given
  (hsymm : ∀ x y, ψ x y = ψ y x)
  (hone : ∀ y, ψ 1 y = 0)
  (hcoc : ∀ x y z, x • ψ y z - ψ (x * y) z + ψ x (y * z) - z • ψ x y = 0) :
-- imply
  ∃ l : S →ₗ[R] M, l 1 = 0 ∧ ∀ x y, ψ x y = l (x * y) - x • l y - y • l x := by
-- proof
  let c : Cocycle R S M := ⟨ψ, hsymm, hone, hcoc⟩
  refine ⟨ell c, ell_one (c := c), fun x y => ψ_eq (c := c) (x := x) (y := y)⟩


-- created on 2026-10-13
