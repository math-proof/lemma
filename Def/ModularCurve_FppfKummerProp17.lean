module
public import Mathlib.Algebra.Exact
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Rank
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Def.Scheme_FppfCohomologyLES
public import Def.AlgebraicGeometry_FppfGmRepresentable
public import Instance.AlgebraicGeometry_FppfKummerProp17
public import Structure.AlgebraicGeometry_FppfKummerProp17
public import Abbrev.AlgebraicGeometry_FppfKummerProp17


public section

namespace ModularCurve


namespace AdmissibleInvariants

variable {p : ℕ}

def eulerDefect (I : AdmissibleInvariants p) : ℤ := (I.h1 : ℤ) - I.h0

def genericDefect (I : AdmissibleInvariants p) : ℤ := (I.δ : ℤ) - I.α

end AdmissibleInvariants

section SixTerm

variable {A B C D E F : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

end SixTerm

end ModularCurve

set_option autoImplicit false

universe w' w v u

open CategoryTheory Abelian Limits

namespace FppfCohomologyLES

section ChainToDevice

variable {A B C D E F : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]

end ChainToDevice

section FppfPropOneSeven

open AlgebraicGeometry Scheme

section WithLocalInstances

variable [HasSheafify Scheme.fppfTopology.{u} Ab.{u + 1}]
  [HasExt.{u + 1} (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1})]


end WithLocalInstances

end FppfPropOneSeven

end FppfCohomologyLES

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace FppfKummerSES

open CategoryTheory AlgebraicGeometry Limits Opposite Polynomial Scheme
open FppfRepresentableGroupSchemeSheaf

def sheafULift :
    Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u} ⥤
      Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} :=
  sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}

def GmAbelianSheafLifted : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} :=
  sheafULift.{u}.obj GmAbelianSheaf.{u}

def gmLiftedSectionsAddEquiv (T : Scheme.{u}) :
    (GmAbelianSheafLifted.{u}.obj.obj (op T) : Type (u + 1)) ≃+
      ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ)) :=
  AddEquiv.refl _

def gmLiftedSectionUnit {T : Scheme.{u}}
    (s : ToType (GmAbelianSheafLifted.{u}.obj.obj (op T))) : ((Γ(T, ⊤) : Type u))ˣ :=
  (s : ULift.{u + 1} (Additive ((Γ(T, ⊤) : Type u)ˣ))).down.toMul

def gmPowMul (p : ℕ) : Gm.{u} ⟶ Gm.{u} where
  app T := CommGrpCat.ofHom (powMonoidHom p)
  naturality T T' f := by
    ext u
    simp only [CommGrpCat.hom_comp, MonoidHom.comp_apply]
    exact (map_pow (Gm.{u}.map f).hom u p).symm

def gmPowAb (p : ℕ) : GmAbelianSheaf.{u} ⟶ GmAbelianSheaf.{u} :=
  ObjectProperty.homMk
    (Functor.whiskerRight (gmPowMul p) commGroupAddCommGroupEquivalence.functor)

def gmPowSelf (p : ℕ) : GmAbelianSheafLifted.{u} ⟶ GmAbelianSheafLifted.{u} :=
  sheafULift.{u}.map (gmPowAb p)

section AffineKummerCover

variable (R : CommRingCat.{u}) (u₀ : (R : Type u)ˣ) (p : ℕ)

def kummerRootUnit (hp : p ≠ 0) : (KummerAlgebra R u₀ p)ˣ :=
  (kummer_root_isUnit R u₀ p hp).unit

def kummerCover : Spec (CommRingCat.of (KummerAlgebra R u₀ p)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap (R : Type u) (KummerAlgebra R u₀ p)))

end AffineKummerCover


section KummerSES

variable (p : ℕ)

def muPAbelianSheafLifted : Sheaf Scheme.fppfTopology.{u} AddCommGrpCat.{u + 1} :=
  kernel (gmPowSelf.{u} p)

def kummerSES : ShortComplex (Sheaf Scheme.fppfTopology.{u} Ab.{u + 1}) :=
  ShortComplex.mk (kernel.ι (gmPowSelf.{u} p)) (gmPowSelf.{u} p) (kernel.condition _)

end KummerSES


section KernelH0

open FppfCohomologyLES

variable (p : ℕ)

def kummerKernelH0AddEquiv (hp : p ≠ 0) :
    FppfH (muPAbelianSheafLifted.{u} p) 0 ≃+
      (cohomologyMap (gmPowSelf.{u} p) 0).ker :=
  (AddMonoidHom.ofInjective (kummer_sixTermLES.{u} p hp).1).trans
    (AddEquiv.addSubgroupCongr
      ((kummer_sixTermLES.{u} p hp).2.1.addMonoidHom_ker_eq.symm))

end KernelH0

end FppfKummerSES

end
