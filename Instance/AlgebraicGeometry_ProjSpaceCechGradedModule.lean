-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ProjSpaceCechGradedModule.lean: instance decls only.
import Mathlib
import Instance.AlgebraicGeometry_ProjSpaceCechTwist
import Lemma.AlgebraicGeometry.ProjSpaceCechGradedModule

set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech


section GradSec

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n) (I : Finset (Fin (n + 1)))

instance GradedModule.Frac.setoid : Setoid (GradedModule.Frac D I) where
  r := GradedModule.Frac.Rel D I
  iseqv := ⟨GradedModule.Frac.Rel.refl D I, GradedModule.Frac.Rel.symm D I,
    GradedModule.Frac.Rel.trans D I⟩

instance GradedModule.sec.instZero : Zero (GradedModule.sec D I) :=
  ⟨GradedModule.sec.mk D I ⟨0, fun _ _ => rfl, 0, by simp⟩⟩

instance GradedModule.sec.instAdd : Add (GradedModule.sec D I) where
  add := Quotient.map₂
    (fun x y => ⟨x.denExp + y.denExp, GradedModule.Frac.supp_add I x.hden y.hden,
      GradedModule.monMul D y.denExp x.num + GradedModule.monMul D x.denExp y.num, by
        have hx := GradedModule.monMul_mem_grade D y.denExp _ x.num x.hnum
        have hy := GradedModule.monMul_mem_grade D x.denExp _ y.num y.hnum
        refine Submodule.add_mem _ ?_ ?_
        · convert hx using 2
          simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
        · convert hy using 2
          simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring⟩)
    (by
      rintro ⟨a, ha, m, hm⟩ ⟨a', ha', m', hm'⟩ ⟨c, hc, heqc⟩
        ⟨b, hb, p, hp⟩ ⟨b', hb', p', hp'⟩ ⟨c', hc', heqc'⟩
      refine ⟨c + c', GradedModule.Frac.supp_add I hc hc', ?_⟩
      simp only [map_add]
      have key1 : GradedModule.monMul D (c + c' + (a' + b'))
          (GradedModule.monMul D b m)
        = GradedModule.monMul D (c + c' + (a + b)) (GradedModule.monMul D b' m') := by
        rw [← GradedModule.monMul_add_apply, ← GradedModule.monMul_add_apply,
          GradedModule.monMul_congr D (b := c' + b' + b + (c + a'))
            (fun j => by simp only [Pi.add_apply]; omega) m,
          GradedModule.monMul_congr D (b := c' + b' + b + (c + a))
            (fun j => by simp only [Pi.add_apply]; omega) m',
          GradedModule.monMul_add_apply (a := c' + b' + b) (b := c + a'),
          GradedModule.monMul_add_apply (a := c' + b' + b) (b := c + a), heqc]
      have key2 : GradedModule.monMul D (c + c' + (a' + b'))
          (GradedModule.monMul D a p)
        = GradedModule.monMul D (c + c' + (a + b)) (GradedModule.monMul D a' p') := by
        rw [← GradedModule.monMul_add_apply, ← GradedModule.monMul_add_apply,
          GradedModule.monMul_congr D (b := c + a' + a + (c' + b'))
            (fun j => by simp only [Pi.add_apply]; omega) p,
          GradedModule.monMul_congr D (b := c + a' + a + (c' + b))
            (fun j => by simp only [Pi.add_apply]; omega) p',
          GradedModule.monMul_add_apply (a := c + a' + a) (b := c' + b'),
          GradedModule.monMul_add_apply (a := c + a' + a) (b := c' + b), heqc']
      rw [key1, key2])

instance GradedModule.sec.instNeg : Neg (GradedModule.sec D I) where
  neg := Quotient.map (fun x => ⟨x.denExp, x.hden, -x.num, by simpa using neg_mem x.hnum⟩)
    (by rintro ⟨a, ha, m, hm⟩ ⟨a', ha', m', hm'⟩ ⟨c, hc, heq⟩;
        exact ⟨c, hc, by simp [map_neg, heq]⟩)

instance GradedModule.sec.instSMul : SMul R (GradedModule.sec D I) where
  smul r := Quotient.map (fun x => ⟨x.denExp, x.hden, r • x.num, Submodule.smul_mem _ r x.hnum⟩)
    (by rintro ⟨a, ha, m, hm⟩ ⟨a', ha', m', hm'⟩ ⟨c, hc, heq⟩;
        exact ⟨c, hc, by simp only [map_smul, heq]⟩)

instance GradedModule.sec.instAddCommGroup : AddCommGroup (GradedModule.sec D I) where
  add_assoc := by
    rintro ⟨x⟩ ⟨y⟩ ⟨z⟩
    refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp only [zero_add, map_add, ← GradedModule.monMul_add_apply]
    rw [show x.denExp + y.denExp + z.denExp = x.denExp + (y.denExp + z.denExp) from
        add_assoc _ _ _,
      add_assoc]
    refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_) <;>
      exact GradedModule.monMul_congr D (fun j => congrFun (by abel) j) _
  zero_add := by
    rintro ⟨x⟩
    refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp [GradedModule.monMul_zero]
  add_zero := by
    rintro ⟨x⟩
    refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp [GradedModule.monMul_zero]
  neg_add_cancel := by
    rintro ⟨x⟩
    refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp
  add_comm := by
    rintro ⟨x⟩ ⟨y⟩
    refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    dsimp only
    rw [zero_add, zero_add, show x.denExp + y.denExp = y.denExp + x.denExp from add_comm _ _,
      add_comm (GradedModule.monMul D y.denExp x.num)]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance GradedModule.sec.instModule : Module R (GradedModule.sec D I) where
  one_smul := by
    rintro ⟨x⟩
    exact (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, by simp⟩
  mul_smul r s := by
    rintro ⟨x⟩
    exact (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, by simp [mul_smul]⟩
  smul_zero r := by
    exact (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, by simp⟩
  smul_add r := by
    rintro ⟨x⟩ ⟨y⟩
    exact (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, by simp [smul_add]⟩
  add_smul r s := by
    rintro ⟨x⟩
    refine (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp only [zero_add, map_add, map_smul, ← GradedModule.monMul_add_apply, add_smul]
  zero_smul := by
    rintro ⟨x⟩
    exact (GradedModule.sec_mk_eq D I).mpr ⟨0, fun _ _ => rfl, by simp⟩

end GradSec

section GradAltC

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

instance GradedModule.H.addCommGroup (i : ℕ) : AddCommGroup (GradedModule.H D i) :=
  match i with
  | 0 => inferInstanceAs (AddCommGroup ↥(LinearMap.ker (GradedModule.d D 0)))
  | (j + 1) => inferInstanceAs (AddCommGroup
      (↥(LinearMap.ker (GradedModule.d D (j + 1))) ⧸ _))

instance GradedModule.H.module (i : ℕ) : Module R (GradedModule.H D i) :=
  match i with
  | 0 => inferInstanceAs (Module R ↥(LinearMap.ker (GradedModule.d D 0)))
  | (j + 1) => inferInstanceAs (Module R
      (↥(LinearMap.ker (GradedModule.d D (j + 1))) ⧸ _))

end GradAltC


end ProjSpaceCech

end
