module

public import Mathlib
public import Instance.Module_CommFamilyAnnPart
public import Structure.Module_CommFamilyAnnPart

public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace Module.End

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (σ : Type*)


variable {K V σ}

namespace CommFamily

variable (F : CommFamily K V σ)


public theorem isMulCommutative_adjoin : IsMulCommutative F.adjoin := by
  refine Algebra.isMulCommutative_adjoin K ?_
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  exact F.comm a b


@[simp] public theorem coe_gen (a : σ) : (F.gen a : Module.End K V) = F.T a := rfl


public theorem eval_apply (Q : MvPolynomial σ K) : F.eval Q = (MvPolynomial.aeval F.gen Q : F.adjoin) := rfl


@[simp] public theorem eval_X (a : σ) : F.eval (MvPolynomial.X a) = F.T a := by
  rw [eval_apply, MvPolynomial.aeval_X, coe_gen]


@[simp] public theorem eval_C (c : K) : F.eval (MvPolynomial.C c) = algebraMap K (Module.End K V) c :=
  F.eval.commutes c


public theorem commute_eval_T (Q : MvPolynomial σ K) (a : σ) : Commute (F.eval Q) (F.T a) := by
  have h := mul_comm (MvPolynomial.aeval F.gen Q : F.adjoin) (F.gen a)
  show F.eval Q * F.T a = F.T a * F.eval Q
  rw [F.eval_apply, ← F.coe_gen a, ← Subalgebra.coe_mul, ← Subalgebra.coe_mul, h]


public theorem eval_mem_adjoin (Q : MvPolynomial σ K) : F.eval Q ∈ F.adjoin :=
  (MvPolynomial.aeval F.gen Q).2


public theorem mem_annPart_iff (p : ℕ) [Fact p.Prime] [CharP K p] (θ : σ → K) (v : V) :
    v ∈ F.annPart p θ ↔ ∀ Q : MvPolynomial σ (ZMod p),
      MvPolynomial.aeval θ (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) = 0 →
        F.eval (MvPolynomial.map (ZMod.castHom (dvd_refl p) K) Q) v = 0 := by
  simp only [annPart, Submodule.mem_iInf, LinearMap.mem_ker]

end CommFamily

end Module.End
