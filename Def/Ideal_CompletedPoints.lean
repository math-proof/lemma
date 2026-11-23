import Mathlib
import Def.AlgHom_Points
import Instance.PDivisibleGroup_CompletedPoints

set_option autoImplicit false

noncomputable section

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section Reduce

variable (p)
variable (S : Type) [CommRing S] [Algebra R S]

variable (R)

def reduceModPow (i : ℕ) :
    (S ⧸ Ideal.span {(p : S) ^ (i + 1)}) →ₐ[R] (S ⧸ Ideal.span {(p : S) ^ i}) :=
  Ideal.Quotient.factorₐ R (span_pow_succ_le p S i)

def mapModPow {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (i : ℕ) :
    (S ⧸ Ideal.span {(p : S) ^ i}) →ₐ[R] (S' ⧸ Ideal.span {(p : S') ^ i}) :=
  Ideal.quotientMapₐ (Ideal.span {(p : S') ^ i}) φ (span_pow_le_comap p S φ i)

end Reduce

variable (G : PDivisibleGroup R p h) (S : Type) [CommRing S] [Algebra R S]

def CPoints : AddSubgroup (∀ i : ℕ, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) where
  carrier := {x | ∀ i, G.pointsMap (reduceModPow R p S i) (x (i + 1)) = x i}
  add_mem' {x y} hx hy i := by rw [Pi.add_apply, Pi.add_apply, map_add, hx i, hy i]
  zero_mem' i := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  neg_mem' {x} hx i := by rw [Pi.neg_apply, Pi.neg_apply, map_neg, hx i]

def cpointsProj (i : ℕ) : G.CPoints S →+ G.Points (S ⧸ Ideal.span {(p : S) ^ i}) where
  toFun x := (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i
  map_zero' := rfl
  map_add' _ _ := rfl

def toCPoints : G.Points S →+ G.CPoints S where
  toFun z := ⟨fun i => G.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) z, fun i => by
    change G.pointsMap (reduceModPow R p S i)
        (G.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ (i + 1)})) z) = _
    rw [← AddMonoidHom.comp_apply, ← pointsMap_comp, reduceModPow_comp_mkₐ]⟩
  map_zero' := Subtype.ext (funext fun i => by simp)
  map_add' x y := Subtype.ext (funext fun i => by simp)

section Map

variable {S}
variable {S' : Type} [CommRing S'] [Algebra R S'] {S'' : Type} [CommRing S''] [Algebra R S'']

def cpointsMap (φ : S →ₐ[R] S') : G.CPoints S →+ G.CPoints S' where
  toFun x := ⟨fun i => G.pointsMap (mapModPow R p S φ i) (G.cpointsProj S i x), fun i => by
    change G.pointsMap (reduceModPow R p S' i)
        (G.pointsMap (mapModPow R p S φ (i + 1)) (G.cpointsProj S (i + 1) x)) = _
    rw [← AddMonoidHom.comp_apply, ← pointsMap_comp, reduceModPow_comp_mapModPow, pointsMap_comp,
      AddMonoidHom.comp_apply, pointsMap_reduceModPow_cpointsProj_succ]⟩
  map_zero' := Subtype.ext (funext fun i => by simp)
  map_add' x y := Subtype.ext (funext fun i => by simp)

end Map

end PDivisibleGroup

end
