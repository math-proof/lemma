import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.Artin
open Representation


/--
[artinEulerProductOfLocalData_eq_of_hasProd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinEulerProductOfLocalData_eq_of_hasProd_eq
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasArtinEulerProduct ρ localData s z) :
-- imply
  artinEulerProductOfLocalData ρ localData s = z := by
-- proof
  apply Representation.artinEulerProductOfLocalData_eq_of_hasProd ρ localData s z h

/--
[HasNonzeroArtinEulerProduct.hasArtinEulerProduct](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma HasNonzeroArtinEulerProduct_hasArtinEulerProduct_eq
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  HasArtinEulerProduct ρ localData s z := by
-- proof
  apply Representation.HasNonzeroArtinEulerProduct.hasArtinEulerProduct h

/--
[HasNonzeroArtinEulerProduct.ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma HasNonzeroArtinEulerProduct_ne_zero_eq
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  z ≠ 0 := by
-- proof
  apply Representation.HasNonzeroArtinEulerProduct.ne_zero h

/--
[artinEulerProductOfLocalData_eq_of_hasNonzeroProd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinEulerProductOfLocalData_eq_of_hasNonzeroProd_eq
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {localData : Nat.Primes → ArtinLocalDatum G}
  {s z : ℂ}
-- given
  (h : HasNonzeroArtinEulerProduct ρ localData s z) :
-- imply
  artinEulerProductOfLocalData ρ localData s = z := by
-- proof
  apply Representation.artinEulerProductOfLocalData_eq_of_hasNonzeroProd ρ localData s z h

/--
[artinLocalFactorRaw_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinLocalFactorRaw_zero_eq
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
  apply Representation.artinLocalFactorRaw_zero ρ p d

/--
[artinLocalFactorRaw_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinLocalFactorRaw_eq_zero_iff_eq
  {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V] [Module.Finite ℂ V]
  {ρ : Representation ℂ G V}
  {p : Nat.Primes}
  {d : ArtinLocalDatum G}
  {s : ℂ} :
-- imply
  artinLocalFactorRaw ρ p d s = 0 ↔ ¬ArtinLocalFactorRegular ρ p d s := by
-- proof
  apply Representation.artinLocalFactorRaw_eq_zero_iff ρ p d s

/--
[artinLocalFactorRaw_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinLocalFactorRaw_ne_zero_eq
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
  apply Representation.artinLocalFactorRaw_ne_zero ρ p d s h

/--
[HasNonzeroArtinEulerProduct.localFactorRegular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma HasNonzeroArtinEulerProduct_localFactorRegular_eq
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
  apply Representation.HasNonzeroArtinEulerProduct.localFactorRegular h p

/--
[artinLocalFactorRaw_of_action_eq_id_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinLocalFactorRaw_of_action_eq_id_general_eq
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
  apply Representation.artinLocalFactorRaw_of_action_eq_id_general ρ p d s hact

/--
[artinLocalFactorRaw_of_action_eq_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/Artin.lean)
-/
@[path]
private lemma artinLocalFactorRaw_of_action_eq_id_eq
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
  apply Representation.artinLocalFactorRaw_of_action_eq_id ρ p d s hact hdim


-- created on 2026-10-20
