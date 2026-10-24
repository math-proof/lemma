import Mathlib.Algebra.Module.Torsion.Basic

set_option autoImplicit false

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]

structure LevelPairing (T : Type) [CommRing T] [Algebra 𝒪 T]
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M] where
  B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪
  selfAdjoint : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n)
  perfect : Function.Bijective B

structure RungDatum (T : Type) [CommRing T] [Algebra 𝒪 T]
    (T' : Type) [CommRing T'] [Algebra 𝒪 T']
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    (M' : Type) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    (P : LevelPairing (𝒪 := 𝒪) T M) (P' : LevelPairing (𝒪 := 𝒪) T' M') where
  res : T' →ₐ[𝒪] T
  i : M →ₗ[𝒪] M'
  j : M' →ₗ[𝒪] M
  Δ : T
  adjoint : ∀ (m' : M') (m : M), P.B (j m') m = P'.B m' (i m)
  comp_eq_smul : ∀ m : M, j (i m) = Δ • m

section Clauses

variable {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

def IharaClauseAt (D : RungDatum T T' M M' P P')
    (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪) : Prop :=
  Submodule.map D.i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
    (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪

def EtaClauseAt (D : RungDatum T T' M M' P P') (πT : T →ₐ[𝒪] 𝒪) (c : 𝒪) : Prop :=
  Ideal.span {πT D.Δ} = Ideal.span {c}

end Clauses

namespace RungAssembly

variable {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

def smulLinear (t : T) : M →ₗ[𝒪] M where
  toFun m := t • m
  map_add' := smul_add t
  map_smul' a m := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul (A := T) (M := M) a m, ← algebraMap_smul (A := T) (M := M) a (t • m),
      smul_smul, smul_smul, mul_comm]

@[simp] lemma smulLinear_apply (t : T) (m : M) : smulLinear (𝒪 := 𝒪) t m = t • m := rfl

variable (P P') in

structure LegDatum (n : ℕ) where
  iLeg : Fin n → (M →ₗ[𝒪] M')
  jLeg : Fin n → (M' →ₗ[𝒪] M)
  adjoint_leg : ∀ (k : Fin n) (m' : M') (m : M), P.B (jLeg k m') m = P'.B m' (iLeg k m)
  table : Fin n → Fin n → T
  htable : ∀ (k k' : Fin n) (m : M), jLeg k (iLeg k' m) = table k k' • m

variable {n : ℕ}

def iComb (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T) : M →ₗ[𝒪] M' :=
  ∑ k, (L.iLeg k).comp (smulLinear (c k))

def jComb (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T) : M' →ₗ[𝒪] M :=
  ∑ k, (smulLinear (c k)).comp (L.jLeg k)

def deltaComb (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T) : T :=
  ∑ k, ∑ k', c k * L.table k k' * c k'

def rungDatumOfLegs (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : RungDatum (𝒪 := 𝒪) T T' M M' P P' where
  res := res
  i := iComb L c
  j := jComb L c
  Δ := deltaComb L c
  adjoint := by
    intro m' m
    simp only [iComb, jComb, LinearMap.sum_apply, LinearMap.comp_apply, smulLinear_apply,
      map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [P.selfAdjoint, L.adjoint_leg]
  comp_eq_smul := by
    intro m
    simp only [iComb, jComb, LinearMap.sum_apply, LinearMap.comp_apply, smulLinear_apply,
      map_sum, deltaComb, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [L.htable, smul_smul, smul_smul]

@[simp] lemma rungDatumOfLegs_res (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).res = res := rfl

@[simp] lemma rungDatumOfLegs_i (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).i = iComb L c := rfl

@[simp] lemma rungDatumOfLegs_j (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).j = jComb L c := rfl

@[simp] lemma rungDatumOfLegs_Δ (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).Δ = deltaComb L c := rfl

end RungAssembly

end IharaTower
