/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib

namespace InverseLimit

/-- A countable inverse system: a sequence of types `obj n` together with transition maps
`map n : obj (n + 1) → obj n`. -/
structure NatInverseSystem where
  obj : ℕ → Type*
  map : ∀ n, obj (n + 1) → obj n

namespace NatInverseSystem

variable (S : NatInverseSystem)

/-- The inverse limit of a `NatInverseSystem` $S$: coherent sequences $(a_n)$ with
$a_n \in S_n$ and $S.\mathrm{map}\,n\,(a_{n+1}) = a_n$. -/
def InverseLimit : Type _ :=
  { a : ∀ n, S.obj n // ∀ n, S.map n (a (n + 1)) = a n }

/-- Canonical projection $\mathrm{proj}_n : \mathrm{InverseLimit}\,S \to S_n$. -/
def proj (n : ℕ) (a : S.InverseLimit) : S.obj n :=
  a.val n

/-- Universal property (lift): a compatible family `g n : X → S.obj n` factors through the
inverse limit. -/
def lift {X : Type*} (g : ∀ n, X → S.obj n)
    (hg : ∀ n x, S.map n (g (n + 1) x) = g n x) : X → S.InverseLimit :=
  fun x => ⟨fun n => g n x, fun n => hg n x⟩

/-- A countable inverse system of commutative rings: a sequence of `CommRing`s with ring
homomorphism transition maps. -/
structure NatRingInverseSystem where
  obj : ℕ → Type*
  [instCommRing : ∀ n, CommRing (obj n)]
  map : ∀ n, obj (n + 1) →+* obj n

attribute [instance] NatRingInverseSystem.instCommRing

namespace NatRingInverseSystem

variable (S : NatRingInverseSystem)

/-- Forget the ring structure on a `NatRingInverseSystem`, viewing it as a `NatInverseSystem`. -/
def toNatInverseSystem : NatInverseSystem where
  obj := S.obj
  map n := S.map n

/-- The inverse limit of a `NatRingInverseSystem` realized as a subring of the product
$\prod_n S_n$, consisting of coherent sequences. -/
def invLimSubring : Subring (∀ n, S.obj n) where
  carrier := { a | ∀ n, S.map n (a (n + 1)) = a n }
  mul_mem' := fun {a b} ha hb n => by
    simp only [Pi.mul_apply, map_mul, ha n, hb n]
  one_mem' := fun n => by
    simp only [Pi.one_apply, map_one]
  add_mem' := fun {a b} ha hb n => by
    simp only [Pi.add_apply, map_add, ha n, hb n]
  zero_mem' := fun n => by
    simp only [Pi.zero_apply, map_zero]
  neg_mem' := fun {a} ha n => by
    simp only [Pi.neg_apply, map_neg, ha n]

/-- The inverse limit of a `NatRingInverseSystem` as a commutative ring (alias for the subring
`invLimSubring`). -/
abbrev InverseLimitRing : Type _ := S.invLimSubring

instance : CommRing S.InverseLimitRing := inferInstance

/-- The $n$-th projection ring homomorphism `InverseLimitRing →+* S.obj n`. -/
def projRingHom (n : ℕ) : S.InverseLimitRing →+* S.obj n :=
  (Pi.evalRingHom (fun n => S.obj n) n).comp S.invLimSubring.subtype

end NatRingInverseSystem

section ZModSystem

/-- The `NatInverseSystem` whose $n$-th object is $\mathbb{Z}/p^{n+1}\mathbb{Z}$ and whose
transition maps are reduction modulo $p^{n+1}$ to $p^n$. -/
noncomputable def zmodInverseSystem (p : ℕ) [Fact (Nat.Prime p)] : NatInverseSystem where
  obj n := ZMod (p ^ (n + 1))
  map n := ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

/-- The `NatRingInverseSystem` whose $n$-th object is the commutative ring
$\mathbb{Z}/p^{n+1}\mathbb{Z}$ with reduction ring homomorphisms. -/
noncomputable def zmodRingInverseSystem (p : ℕ) [Fact (Nat.Prime p)] :
    NatRingInverseSystem where
  obj n := ZMod (p ^ (n + 1))
  map n := ZMod.castHom (pow_dvd_pow p (by omega)) (ZMod (p ^ (n + 1)))

noncomputable instance (p : ℕ) [Fact (Nat.Prime p)] :
    CommRing (zmodRingInverseSystem p).InverseLimitRing :=
  inferInstance

end ZModSystem

end InverseLimit

/-- Definition 4.18 (discrete valuation): a function $v : R \to \mathbb{Z} \cup \{\infty\}$
satisfying $v(a) = \infty \iff a = 0$, $v(ab) = v(a) + v(b)$, and the ultrametric inequality
$\min(v(a), v(b)) \le v(a + b)$. -/
structure DiscreteValuation (R : Type*) [CommRing R] where
  val : R → WithTop ℤ
  val_eq_top_iff : ∀ a : R, val a = ⊤ ↔ a = 0
  val_mul : ∀ a b : R, val (a * b) = val a + val b
  val_add : ∀ a b : R, min (val a) (val b) ≤ val (a + b)

namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

instance : CoeFun (DiscreteValuation R) (fun _ => R → WithTop ℤ) where
  coe v := v.val

/-- Extensionality for discrete valuations: agreement pointwise on $R$ implies equality. -/
@[ext]
theorem ext {v w : DiscreteValuation R} (h : ∀ x, v x = w x) : v = w := by
  cases v; cases w
  congr 1
  funext x
  exact h x

/-- The subring of $\prod_n \mathbb{Z}/p^n\mathbb{Z}$ consisting of compatible sequences with
respect to all reduction maps $\mathbb{Z}/p^n\mathbb{Z} \to \mathbb{Z}/p^m\mathbb{Z}$ for
$m \le n$. This is the explicit inverse-limit model for $\mathbb{Z}_p$. -/
def zmodInvLimSubring : Subring (∀ n, ZMod (p ^ n)) where
  carrier := { a | ∀ (m n : ℕ) (h : m ≤ n),
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) (a n) = a m }
  mul_mem' := fun {a b} ha hb m n hmn => by
    simp only [Pi.mul_apply, map_mul, ha m n hmn, hb m n hmn]
  one_mem' := fun m n hmn => by
    simp only [Pi.one_apply, map_one]
  add_mem' := fun {a b} ha hb m n hmn => by
    simp only [Pi.add_apply, map_add, ha m n hmn, hb m n hmn]
  zero_mem' := fun m n hmn => by
    simp only [Pi.zero_apply, map_zero]
  neg_mem' := fun {a} ha m n hmn => by
    simp only [Pi.neg_apply, map_neg, ha m n hmn]

/-- The $n$-th projection ring homomorphism from `zmodInvLimSubring` to $\mathbb{Z}/p^n\mathbb{Z}$.
-/
def invLimProj (n : ℕ) : (zmodInvLimSubring p) →+* ZMod (p ^ n) :=
  (Pi.evalRingHom (fun n => ZMod (p ^ n)) n).comp (zmodInvLimSubring p).subtype

omit hp in
/-- Compatibility of the projections: the reduction $\mathbb{Z}/p^n\mathbb{Z} \to
\mathbb{Z}/p^m\mathbb{Z}$ composed with `invLimProj p n` equals `invLimProj p m` for $m \le n$. -/
theorem invLimProj_compat (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp (invLimProj p n) =
      invLimProj p m := by
  ext ⟨a, ha⟩
  simp only [invLimProj, RingHom.comp_apply, Pi.evalRingHom_apply, Subring.coe_subtype]
  exact ha m n h

/-- Forward map of the isomorphism $\mathbb{Z}_p \simeq \varprojlim \mathbb{Z}/p^n\mathbb{Z}$:
sends $x \in \mathbb{Z}_p$ to the compatible sequence of its reductions modulo $p^n$. -/
def padicIntToInvLim : ℤ_[p] →+* (zmodInvLimSubring p) where
  toFun x := ⟨fun n => toZModPow n x, fun m n h =>
    RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n h) x⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' x y := Subtype.ext (funext fun _ => map_mul _ x y)
  map_add' x y := Subtype.ext (funext fun _ => map_add _ x y)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)

/-- Inverse map of the isomorphism $\mathbb{Z}_p \simeq \varprojlim \mathbb{Z}/p^n\mathbb{Z}$:
obtained via the universal property `PadicInt.lift` from the family of compatible projections. -/
def invLimToPadicInt : (zmodInvLimSubring p) →+* ℤ_[p] :=
  PadicInt.lift (invLimProj_compat p)

/-- Theorem 4.6 (inverse-limit description): the ring isomorphism $\mathbb{Z}_p \simeq
\varprojlim_n \mathbb{Z}/p^n\mathbb{Z}$. -/
def padicIntEquivInvLim : ℤ_[p] ≃+* (zmodInvLimSubring p) :=
  RingEquiv.ofRingHom
    (padicIntToInvLim p)
    (invLimToPadicInt p)
    (RingHom.ext fun a => by
      ext n
      simp only [padicIntToInvLim, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        RingHom.comp_apply, RingHom.id_apply]
      change (toZModPow n) (PadicInt.lift (invLimProj_compat p) a) = (a : ∀ n, ZMod (p ^ n)) n
      rw [show (toZModPow n) (PadicInt.lift (invLimProj_compat p) a) =
        ((toZModPow n).comp (PadicInt.lift (invLimProj_compat p))) a from rfl,
        PadicInt.lift_spec]
      rfl)
    (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, RingHom.id_apply]
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      change (toZModPow n) (PadicInt.lift (invLimProj_compat p) (padicIntToInvLim p x)) = _
      rw [show (toZModPow n) (PadicInt.lift (invLimProj_compat p) (padicIntToInvLim p x)) =
        ((toZModPow n).comp (PadicInt.lift (invLimProj_compat p))) (padicIntToInvLim p x) from rfl,
        PadicInt.lift_spec]
      simp [invLimProj, padicIntToInvLim])

instance : CommRing (zmodInvLimSubring p) := inferInstance

/-- Reducible alias for the commutative ring structure on $\mathbb{Z}_p$. -/
@[reducible] def padicInt_commRing : CommRing ℤ_[p] := inferInstance

end

end PadicIntegers

namespace PadicUnits

noncomputable section

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The group of units of $\mathbb{Z}_p$, abbreviated `padicUnits p`. -/
abbrev padicUnits : Type := (ℤ_[p])ˣ

instance : Group (padicUnits p) := inferInstance

instance : CommGroup (padicUnits p) := inferInstance

end

end PadicUnits

namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The $n$-th digit in the $p$-adic expansion of $a \in \mathbb{Z}_p$, defined via the
`PadicInt.appr` natural-number approximation. -/
noncomputable def padicDigit (a : ℤ_[p]) (n : ℕ) : ℕ :=
  (a.appr (n + 1) - a.appr n) / p ^ n

/-- Each $p$-adic digit lies in $\{0, 1, \ldots, p-1\}$. -/
theorem padicDigit_lt (a : ℤ_[p]) (n : ℕ) : padicDigit a n < p := by
  unfold padicDigit
  obtain ⟨k, hk⟩ := dvd_appr_sub_appr a n (n + 1) (Nat.le_succ n)
  rw [hk, Nat.mul_div_cancel_left _ (pos_of_ne_zero (pow_ne_zero n (Nat.Prime.pos hp.out).ne'))]
  have h_sub_lt : a.appr (n + 1) - a.appr n < p ^ (n + 1) :=
    lt_of_le_of_lt (Nat.sub_le _ _) (appr_lt a (n + 1))
  rw [hk, pow_succ] at h_sub_lt
  exact Nat.lt_of_mul_lt_mul_left h_sub_lt

/-- The $p$-adic expansion of $a \in \mathbb{Z}_p$ as a sequence valued in `Fin p`, packaging
`padicDigit` together with the bound `padicDigit_lt`. -/
noncomputable def padicExpansion (a : ℤ_[p]) (n : ℕ) : Fin p :=
  ⟨padicDigit a n, padicDigit_lt a n⟩

/-- Given a sequence of digits $b : \mathbb{N} \to \mathrm{Fin}\,p$, the partial sum
$\sum_{k<n} b_k\,p^k \in \mathbb{Z}$. -/
noncomputable def digitPartialSum (b : ℕ → Fin p) (n : ℕ) : ℤ :=
  ∑ k ∈ range n, (b k).val * (p : ℤ) ^ k


/-- The reduction $\mathbb{Z}_p \twoheadrightarrow \mathbb{Z}/p^m\mathbb{Z}$ is surjective. -/
theorem PadicInt.toZModPow_surjective (m : ℕ) :
    Function.Surjective (toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) := by
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨n, by simp [toZModPow, toZModHom]⟩

/-- Ring isomorphism $\mathbb{Z}_p / (p^m) \simeq \mathbb{Z}/p^m\mathbb{Z}$ obtained from the
first isomorphism theorem applied to `toZModPow m`. -/
noncomputable def PadicInt.quotientSpanPowPEquivZMod (m : ℕ) :
    ℤ_[p] ⧸ (Ideal.span {(p : ℤ_[p]) ^ m}) ≃+* ZMod (p ^ m) := by
  rw [← ker_toZModPow m]
  exact RingHom.quotientKerEquivOfSurjective (PadicInt.toZModPow_surjective m)

end Theorem48
open PadicInt in
/-- Corollary 4.9: the ring isomorphism $\mathbb{Z}_p / (p^m) \simeq \mathbb{Z}/p^m\mathbb{Z}$. -/
noncomputable def PadicInt.corollary_4_9 (p : ℕ) [Fact p.Prime] (m : ℕ) :
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m} ≃+* ZMod (p ^ m) := by
  rw [← ker_toZModPow (p := p) m]
  exact RingHom.quotientKerEquivOfSurjective (PadicInt.toZModPow_surjective m)

section PadicValuation

noncomputable section

open PadicInt Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The $p$-adic valuation on $\mathbb{Z}_p$ extended to $\mathbb{N} \cup \{\infty\}$:
$v(0) = \infty$ and $v(a) = \mathrm{PadicInt.valuation}(a)$ otherwise. -/
def padicValuationDef (a : ℤ_[p]) : WithTop ℕ :=
  if a = 0 then ⊤ else ↑(PadicInt.valuation a)
