module

public import Mathlib
public import Theorem.AlgHom.Points
public import Instance.PDivisibleGroup_CompletedPoints

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace PDivisibleGroup

variable {R : Type} [CommRing R] {p h : ℕ}

section Reduce

variable (p)
variable (S : Type) [CommRing S] [Algebra R S]

public theorem span_pow_succ_le (i : ℕ) :
    Ideal.span {(p : S) ^ (i + 1)} ≤ Ideal.span {(p : S) ^ i} :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ i))


public theorem span_pow_le_comap {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (i : ℕ) :
    Ideal.span {(p : S) ^ i} ≤ (Ideal.span {(p : S') ^ i}).comap φ := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
    map_natCast]
  exact Ideal.mem_span_singleton_self _

variable (R)


@[simp] public theorem reduceModPow_mk (i : ℕ) (s : S) :
    reduceModPow R p S i (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ s := rfl


public theorem reduceModPow_comp_mkₐ (i : ℕ) :
    (reduceModPow R p S i).comp (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ (i + 1)})) =
      Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i}) := rfl


@[simp] public theorem mapModPow_mk {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') (i : ℕ)
    (s : S) : mapModPow R p S φ i (Ideal.Quotient.mk _ s) = Ideal.Quotient.mk _ (φ s) := rfl


public theorem mapModPow_id (i : ℕ) : mapModPow R p S (AlgHom.id R S) i = AlgHom.id R _ := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rfl


public theorem mapModPow_comp {S' S'' : Type} [CommRing S'] [Algebra R S'] [CommRing S''] [Algebra R S'']
    (φ : S →ₐ[R] S') (ψ : S' →ₐ[R] S'') (i : ℕ) :
    mapModPow R p S (ψ.comp φ) i = (mapModPow R p S' ψ i).comp (mapModPow R p S φ i) := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rfl


public theorem reduceModPow_comp_mapModPow {S' : Type} [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
    (i : ℕ) :
    (reduceModPow R p S' i).comp (mapModPow R p S φ (i + 1)) =
      (mapModPow R p S φ i).comp (reduceModPow R p S i) := by
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun s => ?_)
  rfl

end Reduce

variable (G : PDivisibleGroup R p h) (S : Type) [CommRing S] [Algebra R S]


public theorem mem_cpoints_iff (x : ∀ i : ℕ, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) :
    x ∈ G.CPoints S ↔ ∀ i, G.pointsMap (reduceModPow R p S i) (x (i + 1)) = x i := Iff.rfl


public theorem CPoints.pointsMap_reduceModPow_succ (x : G.CPoints S) (i : ℕ) :
    G.pointsMap (reduceModPow R p S i) ((x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) (i + 1)) =
      (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i :=
  x.2 i


@[ext] public theorem CPoints.ext {x y : G.CPoints S}
    (hxy : ∀ i, (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i =
      (y : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i) : x = y :=
  Subtype.ext (funext hxy)


public theorem cpointsProj_apply (i : ℕ) (x : G.CPoints S) :
    G.cpointsProj S i x = (x : ∀ i, G.Points (S ⧸ Ideal.span {(p : S) ^ i})) i := rfl


@[simp] public theorem pointsMap_reduceModPow_cpointsProj_succ (i : ℕ) (x : G.CPoints S) :
    G.pointsMap (reduceModPow R p S i) (G.cpointsProj S (i + 1) x) = G.cpointsProj S i x :=
  x.2 i


public theorem cpointsProj_ext {x y : G.CPoints S} (hxy : ∀ i, G.cpointsProj S i x = G.cpointsProj S i y) :
    x = y :=
  CPoints.ext G S hxy


public theorem cpointsProj_zero (x : G.CPoints S) : G.cpointsProj S 0 x = 0 := by
  have h1 : Ideal.span {(p : S) ^ 0} = ⊤ := by rw [pow_zero, Ideal.span_singleton_one]
  haveI : Subsingleton (S ⧸ Ideal.span {(p : S) ^ 0}) :=
    Ideal.Quotient.subsingleton_iff.mpr h1

  have hpt : ∀ (v : ℕ) (f : G.Point (S ⧸ Ideal.span {(p : S) ^ 0}) v), f = 1 := fun v f =>
    Point.ext fun a => Subsingleton.elim _ _
  induction (G.cpointsProj S 0 x) using Points.induction_on with
  | ih v f => rw [hpt v f, ofMul_one, map_zero]


@[simp] public theorem cpointsProj_toCPoints (i : ℕ) (z : G.Points S) :
    G.cpointsProj S i (G.toCPoints S z) =
      G.pointsMap (Ideal.Quotient.mkₐ R (Ideal.span {(p : S) ^ i})) z := rfl

section Map

variable {S}
variable {S' : Type} [CommRing S'] [Algebra R S'] {S'' : Type} [CommRing S''] [Algebra R S'']


@[simp] public theorem cpointsProj_cpointsMap (φ : S →ₐ[R] S') (i : ℕ) (x : G.CPoints S) :
    G.cpointsProj S' i (G.cpointsMap φ x) = G.pointsMap (mapModPow R p S φ i) (G.cpointsProj S i x) :=
  rfl


public theorem cpointsMap_id : G.cpointsMap (AlgHom.id R S) = AddMonoidHom.id _ := by
  refine AddMonoidHom.ext fun x => cpointsProj_ext G S fun i => ?_
  rw [cpointsProj_cpointsMap, mapModPow_id, pointsMap_id]
  rfl


public theorem cpointsMap_comp (φ : S →ₐ[R] S') (ψ : S' →ₐ[R] S'') :
    G.cpointsMap (ψ.comp φ) = (G.cpointsMap ψ).comp (G.cpointsMap φ) := by
  refine AddMonoidHom.ext fun x => cpointsProj_ext G S'' fun i => ?_
  rw [cpointsProj_cpointsMap, mapModPow_comp, pointsMap_comp]
  rfl


public theorem cpointsMap_toCPoints (φ : S →ₐ[R] S') (z : G.Points S) :
    G.cpointsMap φ (G.toCPoints S z) = G.toCPoints S' (G.pointsMap φ z) := by
  refine cpointsProj_ext G S' fun i => ?_
  rw [cpointsProj_cpointsMap, cpointsProj_toCPoints, cpointsProj_toCPoints, ← AddMonoidHom.comp_apply,
    ← AddMonoidHom.comp_apply, ← pointsMap_comp, ← pointsMap_comp]
  rfl

end Map


public theorem CPoints.smul_def (σ : S ≃ₐ[R] S) (x : G.CPoints S) :
    σ • x = G.cpointsMap (σ : S →ₐ[R] S) x := rfl


public theorem CPoints.smul_toCPoints (σ : S ≃ₐ[R] S) (z : G.Points S) :
    σ • G.toCPoints S z = G.toCPoints S (σ • z) := by
  rw [CPoints.smul_def, cpointsMap_toCPoints, Points.smul_def]

end PDivisibleGroup

end
