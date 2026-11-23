module

public import Mathlib
public import Def.WeierstrassCurve_VariableChangePointEquiv
public import Def.WeierstrassCurve_RatPointHom
public import Structure.ModularCurve_ModuliPoint

@[expose] public section

noncomputable section

namespace ModularCurve

open WeierstrassCurve WeierstrassCurve.Affine

section Pairs

variable (N : ℕ) (L : Type*) [Field L] [DecidableEq L]


variable {N L}

def Gamma0Pair.Step (P Q : Gamma0Pair N L) : Prop :=
  ∃ γ : VariableChange L, ∃ _ : γ • P.toCurve = Q.toCurve, ∃ k : ℕ, k.Coprime N ∧
    HEq Q.gen (k • Point.vcInvFun γ P.toCurve.toAffine P.gen)

variable (N L) in

def ModuliPoint : Type _ := Quot (Gamma0Pair.Step (N := N) (L := L))

noncomputable def ModuliPoint.j : ModuliPoint N L → L :=
  Quot.lift (fun P => P.toCurve.j) fun P Q h => by
    obtain ⟨γ, hγ, -⟩ := h
    show P.toCurve.j = Q.toCurve.j
    simp_rw [← hγ, variableChange_j]

end Pairs


section Map

variable {L L' : Type} [Field L] [Field L']
variable [DecidableEq L] [DecidableEq L']

variable {N : ℕ}

def gamma0PairMap (σ : L →+* L') (P : Gamma0Pair N L) : Gamma0Pair N L' where
  toCurve := P.toCurve.map σ
  isElliptic := inferInstance
  gen := WeierstrassCurve.ratPointMap σ (W₀ := P.toCurve) P.gen
  addOrderOf_gen := (addOrderOf_ratPointMap σ P.toCurve P.gen).trans P.addOrderOf_gen

def moduliPointMapRingHom (σ : L →+* L') : ModuliPoint N L → ModuliPoint N L' :=
  Quot.lift (fun P => (Quot.mk _ (gamma0PairMap σ P) : ModuliPoint N L'))
    fun _ _ h => Quot.sound (gamma0PairStep_map σ h)

end Map

end ModularCurve

end

end
