module

public import Mathlib
public import Theorem.LinearMap.ProjSpaceCechTwist
public import Instance.AlgebraicGeometry_ProjSpaceCechGradedModule
public import Structure.AlgebraicGeometry_ProjSpaceCechGradedModule
public import Abbrev.AlgebraicGeometry_ProjSpaceCechGradedModule

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

section Carrier

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}
variable (D : GradedModule R n)

public theorem GradedModule.xMul_pow_commute (j k : Fin (n + 1)) (a b : ℕ) :
    Commute (D.xMul j ^ a) (D.xMul k ^ b) := by
  exact (Commute.pow_pow · a b) <| show D.xMul j * D.xMul k = D.xMul k * D.xMul j from
    D.xMul_comm j k


public theorem GradedModule.monMul_congr {a b : Fin (n + 1) → ℕ} (h : ∀ j, a j = b j) (m : D.M) :
    GradedModule.monMul D a m = GradedModule.monMul D b m := by
  rw [show a = b from funext h]


public theorem GradedModule.noncommProd_one (s : Finset (Fin (n + 1)))
    (f : Fin (n + 1) → (D.M →ₗ[R] D.M)) (hc : _) (hf : ∀ j ∈ s, f j = 1) :
    s.noncommProd f hc = 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj,
      hf j (Finset.mem_insert_self j s),
      ih (hc.mono (by simp [Finset.subset_insert]))
        (fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      one_mul]


public theorem GradedModule.monMul_zero :
    GradedModule.monMul D 0 = LinearMap.id := by
  exact GradedModule.noncommProd_one D _ _ _ (fun j _ => by simp)


public theorem GradedModule.monMul_add (a b : Fin (n + 1) → ℕ) :
    GradedModule.monMul D (a + b)
      = GradedModule.monMul D a * GradedModule.monMul D b := by
  unfold GradedModule.monMul
  rw [← Finset.noncommProd_mul_distrib]
  · exact Finset.noncommProd_congr rfl (fun j _ => by simp [Pi.add_apply, pow_add]) _
  · intro j _ k _ _; exact (GradedModule.xMul_pow_commute D k j (a k) (b j)).symm


public theorem GradedModule.monMul_add_apply (a b : Fin (n + 1) → ℕ) (m : D.M) :
    GradedModule.monMul D (a + b) m
      = GradedModule.monMul D a (GradedModule.monMul D b m) := by
  rw [GradedModule.monMul_add]; rfl


public theorem GradedModule.monMul_single (j : Fin (n + 1)) (k : ℕ) :
    GradedModule.monMul D (Pi.single j k) = D.xMul j ^ k := by
  have hkey : GradedModule.monMul D (Pi.single j k)
      = (insert j (Finset.univ.erase j)).noncommProd
          (fun i => D.xMul i ^ Pi.single j k i)
          (fun a _ b _ _ => GradedModule.xMul_pow_commute D a b _ _) :=
    Finset.noncommProd_congr (Finset.insert_erase (mem_univ j)).symm (fun _ _ => rfl) _
  rw [hkey, Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.notMem_erase j _),
    GradedModule.noncommProd_one D _ _ _
      (fun i hi => by simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]),
    mul_one, Pi.single_eq_same]


public theorem GradedModule.xMul_pow_mem_grade (j : Fin (n + 1)) (k : ℕ) (d : ℤ) :
    ∀ m ∈ D.grade d, (D.xMul j ^ k) m ∈ D.grade (d + k) := by
  induction k with
  | zero => intro m hm; simpa using hm
  | succ k' ihk =>
    intro m hm
    have h1 := D.xMul_mem_grade j (d + k') _ (ihk m hm)
    have h2 : (D.xMul j ^ (k' + 1)) m = D.xMul j ((D.xMul j ^ k') m) := by
      rw [pow_succ']; rfl
    rw [h2]; convert h1 using 2; push_cast; ring


public theorem GradedModule.monMul_mem_grade (a : Fin (n + 1) → ℕ) (d : ℤ) :
    ∀ m ∈ D.grade d, GradedModule.monMul D a m ∈ D.grade (d + ∑ j, (a j : ℤ)) := by
  unfold GradedModule.monMul
  suffices h : ∀ (s : Finset (Fin (n + 1))) (hc : _), ∀ m ∈ D.grade d,
      (s.noncommProd (fun j => D.xMul j ^ a j) hc) m ∈ D.grade (d + ∑ j ∈ s, (a j : ℤ)) by
    exact h Finset.univ _
  intro s
  induction s using Finset.induction with
  | empty => intro _ m hm; simpa using hm
  | insert j s hj ih =>
    intro hc m hm
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Finset.sum_insert hj]
    have hc' : (↑s : Set (Fin (n + 1))).Pairwise (Commute on fun k => D.xMul k ^ a k) :=
      hc.mono (by simp [Finset.subset_insert])
    have h1 := GradedModule.xMul_pow_mem_grade D j (a j) (d + ∑ i ∈ s, (a i : ℤ))
      ((s.noncommProd (fun k => D.xMul k ^ a k) hc') m) (ih hc' m hm)
    have hmul : ((D.xMul j ^ a j) * s.noncommProd (fun k => D.xMul k ^ a k) hc') m
        = (D.xMul j ^ a j) ((s.noncommProd (fun k => D.xMul k ^ a k) hc') m) := rfl
    rw [hmul]
    convert h1 using 2; push_cast; ring


public theorem GradedModule.monMul_commute (a b : Fin (n + 1) → ℕ) :
    Commute (GradedModule.monMul D a) (GradedModule.monMul D b) := by
  show GradedModule.monMul D a * GradedModule.monMul D b
    = GradedModule.monMul D b * GradedModule.monMul D a
  rw [← GradedModule.monMul_add, ← GradedModule.monMul_add, add_comm]


public theorem GradedModule.monMul_commute_apply (a b : Fin (n + 1) → ℕ) (m : D.M) :
    GradedModule.monMul D a (GradedModule.monMul D b m)
      = GradedModule.monMul D b (GradedModule.monMul D a m) := by
  have := GradedModule.monMul_commute D a b
  exact LinearMap.congr_fun this m

end Carrier

section GradSec

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n) (I : Finset (Fin (n + 1)))


public theorem GradedModule.Frac.supp_add {a b : Fin (n + 1) → ℕ}
    (ha : ∀ j ∉ I, a j = 0) (hb : ∀ j ∉ I, b j = 0) :
    ∀ j ∉ I, (a + b) j = 0 := by
  intro j hj; simp [Pi.add_apply, ha j hj, hb j hj]


public theorem GradedModule.Frac.Rel.refl (x : GradedModule.Frac D I) :
    GradedModule.Frac.Rel D I x x := by
  exact ⟨0, fun _ _ => rfl, rfl⟩


public theorem GradedModule.Frac.Rel.symm {x y : GradedModule.Frac D I}
    (h : GradedModule.Frac.Rel D I x y) : GradedModule.Frac.Rel D I y x := by
  obtain ⟨c, hc, heq⟩ := h
  exact ⟨c, hc, heq.symm⟩


public theorem GradedModule.Frac.Rel.trans {x y z : GradedModule.Frac D I}
    (hxy : GradedModule.Frac.Rel D I x y) (hyz : GradedModule.Frac.Rel D I y z) :
    GradedModule.Frac.Rel D I x z := by
  obtain ⟨c, hc, heqc⟩ := hxy
  obtain ⟨c', hc', heqc'⟩ := hyz
  refine ⟨c + c' + y.denExp,
    GradedModule.Frac.supp_add I (GradedModule.Frac.supp_add I hc hc') y.hden, ?_⟩

  have h1 : GradedModule.monMul D (c + c' + y.denExp + z.denExp) x.num
      = GradedModule.monMul D (c' + z.denExp)
          (GradedModule.monMul D (c + y.denExp) x.num) := by
    rw [← GradedModule.monMul_add_apply]
    exact GradedModule.monMul_congr D (fun j => by simp only [Pi.add_apply]; omega) _
  have h2 : GradedModule.monMul D (c + c' + y.denExp + x.denExp) z.num
      = GradedModule.monMul D (c + x.denExp)
          (GradedModule.monMul D (c' + y.denExp) z.num) := by
    rw [← GradedModule.monMul_add_apply]
    exact GradedModule.monMul_congr D (fun j => by simp only [Pi.add_apply]; omega) _
  rw [h1, h2, heqc, ← heqc']
  exact GradedModule.monMul_commute_apply D _ _ _


public theorem GradedModule.sec_mk_eq {x y : GradedModule.Frac D I} :
    GradedModule.sec.mk D I x = GradedModule.sec.mk D I y
      ↔ GradedModule.Frac.Rel D I x y := by
  exact Quotient.eq


public theorem GradedModule.sec_mk_smul (r : R) (x : GradedModule.Frac D I) :
    r • GradedModule.sec.mk D I x
      = GradedModule.sec.mk D I
          ⟨x.denExp, x.hden, r • x.num, Submodule.smul_mem _ r x.hnum⟩ := by
  rfl


public theorem GradedModule.sec_mk_neg (x : GradedModule.Frac D I) :
    -GradedModule.sec.mk D I x
      = GradedModule.sec.mk D I
          ⟨x.denExp, x.hden, -x.num, by simpa using neg_mem x.hnum⟩ := by
  rfl


public theorem GradedModule.sec_mk_zero_num (a : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    GradedModule.sec.mk D I ⟨a, ha, 0, by simp⟩ = 0 := by
  refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
  simp


public theorem GradedModule.sec_mk_congr {a a' : Fin (n + 1) → ℕ} (ha : ∀ j ∉ I, a j = 0)
    (ha' : ∀ j ∉ I, a' j = 0) (haa : a = a') {m : D.M} (hm : m ∈ D.grade (∑ j, (a j : ℤ))) :
    GradedModule.sec.mk D I ⟨a, ha, m, hm⟩
      = GradedModule.sec.mk D I ⟨a', ha', m, haa ▸ hm⟩ := by
  subst haa; rfl


public theorem GradedModule.sec_mk_add (a : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0)
    {m m' : D.M} (hm : m ∈ D.grade (∑ j, (a j : ℤ))) (hm' : m' ∈ D.grade (∑ j, (a j : ℤ))) :
    GradedModule.sec.mk D I ⟨a, ha, m + m', Submodule.add_mem _ hm hm'⟩
      = GradedModule.sec.mk D I ⟨a, ha, m, hm⟩
        + GradedModule.sec.mk D I ⟨a, ha, m', hm'⟩ := by
  refine ((GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩).symm
  simp only [zero_add, map_add, ← GradedModule.monMul_add_apply]


public theorem GradedModule.secIncl_mk {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (x : GradedModule.Frac D I) :
    GradedModule.secIncl D hIJ (GradedModule.sec.mk D I x)
      = GradedModule.sec.mk D J
          ⟨x.denExp, fun j hj => x.hden j (fun h => hj (hIJ h)), x.num, x.hnum⟩ := by
  rfl


public theorem GradedModule.secIncl_trans {I J K : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (hJK : J ⊆ K) :
    (GradedModule.secIncl D hJK).comp (GradedModule.secIncl D hIJ)
      = GradedModule.secIncl D (hIJ.trans hJK) := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨x⟩ := z; rfl

end GradSec

section GradAltC

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)


public theorem GradedModule.d_apply (i : ℕ) (f : GradedModule.cochain D i)
    (s : Idx n (i + 1)) :
    GradedModule.d D i f s
      = ∑ j : Fin (i + 2), (-1 : R) ^ (j : ℕ) •
          GradedModule.faceRes D s j (f (Idx.face n s j)) := by
  simp only [GradedModule.d, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]


public theorem GradedModule.subsingleton_cohomology_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (GradedModule.H D i) := by
  have hsub : Subsingleton (GradedModule.cochain D i) := by
    have he := Idx.isEmpty_of_lt n hi
    exact ⟨fun f g => funext fun s => (he.false s).elim⟩
  rcases i with _ | j
  · exact absurd hi (Nat.not_lt_zero n)
  · exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
      congrArg _ (Subtype.ext (hsub.elim a.1 b.1))⟩

end GradAltC

section SecInclIrrel

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)


public theorem GradedModule.secIncl_irrel {I J : Finset (Fin (n + 1))} (h₁ h₂ : I ⊆ J) :
    GradedModule.secIncl D h₁ = GradedModule.secIncl D h₂ := by
  rfl

end SecInclIrrel

section Instances

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}


public theorem GradedModule.free_monMul_apply (a : Fin (n + 1) → ℕ)
    (p : MvPolynomial (Fin (n + 1)) R) :
    GradedModule.monMul (GradedModule.free R n) a p = (∏ j, X j ^ a j) * p := by
  suffices h : ∀ (s : Finset (Fin (n + 1))) (hc : _),
      (s.noncommProd (fun j => (GradedModule.free R n).xMul j ^ a j) hc) p
        = (∏ j ∈ s, (X j : MvPolynomial (Fin (n+1)) R) ^ a j) * p from h Finset.univ _
  have hpow : ∀ (j : Fin (n + 1)) (k : ℕ) (q : MvPolynomial (Fin (n + 1)) R),
      ((GradedModule.free R n).xMul j ^ k) q = X j ^ k * q := by
    intro j k q
    induction k with
    | zero => simp only [pow_zero, Module.End.one_apply]; exact (one_mul q).symm
    | succ k' ihk =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, ihk]
      exact (mul_assoc (X j) (X j ^ k') q).symm
  intro s
  induction s using Finset.induction with
  | empty => intro _; simp
  | insert j s hj ih =>
    intro hc
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Finset.prod_insert hj,
      Module.End.mul_apply, ih (hc.mono (by simp [Finset.subset_insert])), hpow]
    exact (mul_assoc (X j ^ a j) (∏ i ∈ s, X i ^ a i) p).symm


public theorem GradedModule.free_monMul_injective (a : Fin (n + 1) → ℕ) :
    Function.Injective (GradedModule.monMul (GradedModule.free R n) a) := by
  intro p q hpq
  rw [GradedModule.free_monMul_apply, GradedModule.free_monMul_apply] at hpq
  have hmon : (∏ j, (X j : MvPolynomial (Fin (n+1)) R) ^ a j)
      = MvPolynomial.monomial (∑ j, Finsupp.single j (a j)) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    exact Finset.prod_congr rfl (fun j _ => MvPolynomial.X_pow_eq_monomial)
  rw [hmon] at hpq
  have hinj : Function.Injective
      (fun p => (MvPolynomial.monomial (∑ j, Finsupp.single j (a j)) (1:R)) * p) := by
    intro p' q' h'
    ext e
    have := congrArg (MvPolynomial.coeff (e + ∑ j, Finsupp.single j (a j))) h'
    simpa [MvPolynomial.coeff_monomial_mul'] using this
  exact hinj hpq

end Instances

section FD

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}


public theorem GradedModule.isHomogeneous_prod_X_pow (e : Fin (n + 1) → ℕ) :
    (∏ j, (X j : MvPolynomial (Fin (n + 1)) R) ^ e j).IsHomogeneous (∑ j, e j) := by
  exact IsHomogeneous.prod _ _ _ (fun j _ => isHomogeneous_X_pow _ _)


public theorem GradedModule.prod_X_pow_mem_freeGrade (e : Fin (n + 1) → ℕ) :
    (∏ j, (X j : MvPolynomial (Fin (n + 1)) R) ^ e j)
      ∈ GradedModule.freeGrade R n (∑ j, (e j : ℤ)) := by
  rw [GradedModule.freeGrade_of_nonneg R n (by positivity), mem_homogeneousSubmodule]
  convert GradedModule.isHomogeneous_prod_X_pow e using 1
  exact_mod_cast Int.toNat_natCast _

end FD

section SubMod

variable {R : Type u} [CommRing R] {n : ℕ}


public theorem GradedModule.Hom.map_monMul (φ : GradedModule.Hom D₁ D₂) (a : Fin (n + 1) → ℕ)
    (m : D₁.M) :
    φ.toLinearMap (GradedModule.monMul D₁ a m) = GradedModule.monMul D₂ a (φ.toLinearMap m) := by
  suffices h : ∀ (s : Finset (Fin (n + 1))) (hc₁ : _) (hc₂ : _),
      φ.toLinearMap ((s.noncommProd (fun j => D₁.xMul j ^ a j) hc₁) m)
        = (s.noncommProd (fun j => D₂.xMul j ^ a j) hc₂) (φ.toLinearMap m) from h Finset.univ _ _
  intro s
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | insert j s hj ih =>
    intro hc₁ hc₂
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Module.End.mul_apply, Module.End.mul_apply]
    have hih := ih (hc₁.mono (by simp [Finset.subset_insert]))
      (hc₂.mono (by simp [Finset.subset_insert]))
    induction a j with
    | zero => simpa using hih
    | succ p ihp =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
        ← LinearMap.comp_apply, φ.xMul_comm j, LinearMap.comp_apply, ihp]


public theorem GradedModule.Hom.secMap_incl (φ : GradedModule.Hom D₁ D₂)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    (GradedModule.secIncl D₂ hIJ).comp (GradedModule.Hom.secMap φ I)
      = (GradedModule.Hom.secMap φ J).comp (GradedModule.secIncl D₁ hIJ) := by
  refine LinearMap.ext fun z => ?_; obtain ⟨x⟩ := z; rfl


public theorem GradedModule.Hom.cochainMap_comm (φ : GradedModule.Hom D₁ D₂) (i : ℕ) :
    (GradedModule.d D₂ i).comp (GradedModule.Hom.cochainMap φ i)
      = (GradedModule.Hom.cochainMap φ (i + 1)).comp (GradedModule.d D₁ i) := by
  refine LinearMap.ext fun f => funext fun s => ?_
  simp only [LinearMap.comp_apply, GradedModule.Hom.cochainMap, LinearMap.pi_apply,
    LinearMap.proj_apply, GradedModule.d_apply, map_sum, map_smul,
    GradedModule.faceRes]
  exact Finset.sum_congr rfl fun j _ => congrArg (((-1 : R) ^ (j : ℕ)) • ·)
    (LinearMap.congr_fun
      (GradedModule.Hom.secMap_incl φ (Idx.img_face_subset n s j))
      (f (Idx.face n s j)))


public theorem GradedModule.Presentation.K_xMul_stable {D : GradedModule R n} (σ : GradedModule.Presentation D)
    (j : Fin (n + 1)) : ∀ m ∈ σ.K, σ.F.xMul j m ∈ σ.K := by
  intro m hm
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, σ.hom.xMul_comm, LinearMap.comp_apply,
    LinearMap.mem_ker.mp hm, map_zero]


@[simp] public theorem GradedModule.Hom.shift_toLinearMap (φ : GradedModule.Hom D₁ D₂) (d₀ : ℤ) :
    (φ.shift d₀).toLinearMap = φ.toLinearMap := rfl

end HomShift

end ProjSpaceCech

end
