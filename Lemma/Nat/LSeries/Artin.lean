import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.Artin
open Representation


namespace Representation

/--
[artinEulerProductOfLocalData_eq_of_hasProd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinEulerProductOfLocalData_eq_of_hasProd
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasArtinEulerProduct ρ localData s z) :
-- imply
  artinEulerProductOfLocalData ρ localData s = z :=
-- proof
  h.tprod_eq

end Representation

namespace Representation

/--
[artinLocalFactorRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinLocalFactorRaw_zero
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {p : Nat.Primes}
  {d : ArtinLocalDatum G} :
-- imply
  artinLocalFactorRaw ρ p d 0 =
    (LinearMap.det (LinearMap.id -
    ((Representation.quotientToInvariants
    (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V)
    d.inertia) d.frobenius)))⁻¹ := by
-- proof
  simp [artinLocalFactorRaw, artinLocalDenominator]

end Representation

namespace Representation

/--
[artinLocalFactorRaw_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinLocalFactorRaw_eq_zero_iff
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {p : Nat.Primes}
  {d : ArtinLocalDatum G}
  {s : ℂ} :
-- imply
  artinLocalFactorRaw ρ p d s = 0 ↔ ¬ArtinLocalFactorRegular ρ p d s := by
-- proof
  simp [artinLocalFactorRaw, ArtinLocalFactorRegular]

end Representation

namespace Representation

/--
[artinLocalFactorRaw_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinLocalFactorRaw_ne_zero
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {p : Nat.Primes}
  {d : ArtinLocalDatum G}
  {s : ℂ}
-- given
  (h : ArtinLocalFactorRegular ρ p d s) :
-- imply
  artinLocalFactorRaw ρ p d s ≠ 0 := by
-- proof
  intro hzero
  exact (artinLocalFactorRaw_eq_zero_iff ρ p d s).mp hzero h

end Representation

namespace Representation

/--
[artinLocalFactorRaw_of_action_eq_id_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinLocalFactorRaw_of_action_eq_id_general
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {p : Nat.Primes}
  {d : ArtinLocalDatum G}
  {s : ℂ}
-- given
  (hact : (Representation.quotientToInvariants (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V) d.inertia) d.frobenius = LinearMap.id) :
-- imply
  artinLocalFactorRaw ρ p d s =
    ((1 - (p.1 : ℂ) ^ (-s)) ^ Module.finrank ℂ (invariants
    ((ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V).comp
    d.inertia.subtype)))⁻¹ := by
-- proof
  rw [artinLocalFactorRaw, artinLocalDenominator, hact]
  let W := invariants
    ((ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V).comp
      d.inertia.subtype)
  have hlin : (LinearMap.id : W →ₗ[ℂ] W) -
    (p.1 : ℂ) ^ (-s) • LinearMap.id =
    (1 - (p.1 : ℂ) ^ (-s)) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change x.1 - (p.1 : ℂ) ^ (-s) • x.1 =
      (1 - (p.1 : ℂ) ^ (-s)) • x.1
    rw [sub_smul, one_smul]
  rw [hlin, LinearMap.det_smul, LinearMap.det_id, mul_one]

end Representation

namespace Representation

/--
[artinLocalFactorRaw_of_action_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinLocalFactorRaw_of_action_eq_id
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {p : Nat.Primes}
  {d : ArtinLocalDatum G}
  {s : ℂ}
-- given
  (hact : (Representation.quotientToInvariants (ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V) d.inertia) d.frobenius = LinearMap.id)
  (hdim : Module.finrank ℂ (invariants ((ρ.comp d.decomposition.subtype : Representation ℂ d.decomposition V).comp d.inertia.subtype)) = 1) :
-- imply
  artinLocalFactorRaw ρ p d s = (1 - (p.1 : ℂ) ^ (-s))⁻¹ := by
-- proof
  rw [artinLocalFactorRaw_of_action_eq_id_general ρ p d s hact, hdim, pow_one]

end Representation

/--
[HasNonzeroArtinEulerProduct.hasArtinEulerProduct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma HasNonzeroArtinEulerProduct.hasArtinEulerProduct
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  HasArtinEulerProduct ρ localData s z :=
-- proof
  h.1


namespace Representation

/--
[HasNonzeroArtinEulerProduct.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma HasNonzeroArtinEulerProduct.ne_zero
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  z ≠ 0 :=
-- proof
  h.2

end Representation

namespace Representation

/--
[artinEulerProductOfLocalData_eq_of_hasNonzeroProd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma artinEulerProductOfLocalData_eq_of_hasNonzeroProd
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  artinEulerProductOfLocalData ρ localData s = z :=
-- proof
  h.hasArtinEulerProduct.tprod_eq

end Representation

namespace Representation

/--
[HasNonzeroArtinEulerProduct.localFactorRegular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
lemma HasNonzeroArtinEulerProduct.localFactorRegular
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
  {p : Nat.Primes}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  ArtinLocalFactorRegular ρ p (localData p) s := by
-- proof
  by_contra hp
  have hfactor : artinLocalFactorRaw ρ p (localData p) s = 0 :=
    (artinLocalFactorRaw_eq_zero_iff ρ p (localData p) s).2 hp
  have hzero : HasProd (fun q => artinLocalFactorRaw ρ q (localData q) s) 0 :=
    hasProd_zero_of_exists_eq_zero ⟨p, hfactor⟩
  exact h.ne_zero (h.hasArtinEulerProduct.unique hzero)

end Representation


-- created on 2026-10-20
-- updated on 2026-10-23
