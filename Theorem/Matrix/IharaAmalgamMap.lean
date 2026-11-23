module

public import Theorem.Matrix.IharaAmalgam
public import Theorem.Matrix.Main

public section

namespace Ihara

open Matrix CongruenceSubgroup

open scoped MatrixGroups

variable (N q : ℕ)


@[simp]
public theorem coe_slToAway (g : SL(2, ℤ)) :
    ((slToAway q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      ((g : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl


public theorem algebraMap_ZAway_injective {q : ℕ} (hq : q ≠ 0) :
    Function.Injective (algebraMap ℤ (ZAway q)) :=
  IsLocalization.injective (M := Submonoid.powers (q : ℤ)) (ZAway q)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Int.natCast_ne_zero.mpr hq))


public theorem slToAway_injective {q : ℕ} (hq : q ≠ 0) : Function.Injective (slToAway q) := by
  intro g h hgh
  have hmat := congrArg (fun x : SL(2, ZAway q) => (x : Matrix (Fin 2) (Fin 2) (ZAway q))) hgh
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have hij := congrFun (congrFun hmat i) j
  simp only [coe_slToAway, map_apply] at hij
  exact algebraMap_ZAway_injective hq hij


@[simp]
public theorem coe_vertexZero (g : Gamma0 N) :
    ((vertexZero N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) :=
  rfl


public theorem coe_vertexOne (g : Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      wMat q * (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) *
        wMatInv q :=
  rfl


public theorem wMat_mul_mul_wMatInv (M : Matrix (Fin 2) (Fin 2) (ZAway q)) :
    wMat q * M * wMatInv q =
      !![M 0 0, M 0 1 * IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * M 1 0, M 1 1] := by
  conv_lhs => rw [Matrix.eta_fin_two M]
  rw [wMat, wMatInv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [one_mul, zero_mul, mul_zero, add_zero, zero_add, mul_one]
  rw [mul_right_comm (q : ZAway q) (M 1 1), q_mul_invSelf, one_mul]


public theorem coe_vertexOne_eq (g : Gamma0 N) :
    ((vertexOne N q g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) =
      !![algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 0 1) *
           IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ);
         (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0),
         algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 1)] := by
  rw [coe_vertexOne, wMat_mul_mul_wMatInv]
  rfl


public theorem map_wInt_eq_wMat :
    (!![(1 : ℤ), 0; 0, (q : ℤ)]).map (algebraMap ℤ (ZAway q)) = wMat q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]


public theorem vertex_compat : (vertexZero N q).comp (ι₀ N q) = (vertexOne N q).comp (ι₁ N q) := by
  ext γ : 1
  apply Subtype.ext
  show (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (algebraMap ℤ (ZAway q)) =
    wMat q * ((((ι₁ N q γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map
      (algebraMap ℤ (ZAway q)) * wMatInv q
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ (ZAway q)))
    (w_mul_iota1 N q γ)
  simp only [Matrix.map_mul, map_wInt_eq_wMat] at h
  rw [h, mul_assoc, wMat_mul_wMatInv, mul_one]


public theorem amalgamToAway_vertex_zero (g : Gamma0 N) :
    amalgamToAway N q (iharaVertex N q 0 g) = vertexZero N q g :=
  iharaLift_vertex_zero _ _ _ g


public theorem amalgamToAway_vertex_one (g : Gamma0 N) :
    amalgamToAway N q (iharaVertex N q 1 g) = vertexOne N q g :=
  iharaLift_vertex_one _ _ _ g


public theorem amalgamToAway_base (γ : Gamma0 (N * q)) :
    amalgamToAway N q (iharaBase N q γ) = slToAway q γ :=
  iharaLift_base _ _ _ γ


public theorem N_dvd_entry (g : Gamma0 N) : (N : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := by
  have h := g.2
  rw [Gamma0_mem, CharP.intCast_eq_zero_iff (ZMod N) N] at h
  exact h


public theorem vertexZero_mem (g : Gamma0 N) : vertexZero N q g ∈ Gamma0Away N q := by
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨algebraMap ℤ (ZAway q) k, ?_⟩
  show algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) = _
  rw [hk, map_mul]
  simp


public theorem vertexOne_apply_one_zero (g : Gamma0 N) :
    (vertexOne N q g : SL(2, ZAway q)) 1 0 =
      (q : ZAway q) * algebraMap ℤ (ZAway q) ((g : SL(2, ℤ)) 1 0) := by
  rw [coe_vertexOne_eq]
  rfl


public theorem vertexOne_mem (g : Gamma0 N) : vertexOne N q g ∈ Gamma0Away N q := by
  rw [mem_Gamma0Away, vertexOne_apply_one_zero]
  obtain ⟨k, hk⟩ := N_dvd_entry N g
  refine ⟨(q : ZAway q) * algebraMap ℤ (ZAway q) k, ?_⟩
  rw [hk, map_mul, eq_intCast, Int.cast_natCast]
  ring


public theorem range_amalgamToAway_le : (amalgamToAway N q).range ≤ Gamma0Away N q := by
  rw [MonoidHom.range_eq_map, ← iharaVertex_range_sup, Subgroup.map_sup, sup_le_iff,
    MonoidHom.map_range, MonoidHom.map_range]
  constructor
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, amalgamToAway_vertex_zero]
    exact vertexZero_mem N q g
  · rintro _ ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, amalgamToAway_vertex_one]
    exact vertexOne_mem N q g


public theorem amalgamToAway_mem (x : iharaAmalgam N q) : amalgamToAway N q x ∈ Gamma0Away N q :=
  range_amalgamToAway_le N q ⟨x, rfl⟩


@[simp]
public theorem coe_amalgamToGamma0Away (x : iharaAmalgam N q) :
    ((amalgamToGamma0Away N q x : Gamma0Away N q) : SL(2, ZAway q)) = amalgamToAway N q x :=
  rfl


public theorem amalgamToGamma0Away_injective_iff :
    Function.Injective (amalgamToGamma0Away N q) ↔ Function.Injective (amalgamToAway N q) :=
  MonoidHom.injective_codRestrict _ _ _

end Ihara
