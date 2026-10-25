import Lemma.Definitions.Def_EllipticCurve_FunctionFieldPullback
import Def.EllipticCurve_WeilPairingFun


namespace WeierstrassCurve.Affine

section WeilPairingDefs

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

open Classical in


theorem placeIdeal_zero : placeIdeal W K 0 = ⊤ := dif_pos rfl

theorem placeIdeal_of_ne_zero {P : (W⁄K).Point} (hP : P ≠ 0) :
    placeIdeal W K P = (placeOf W K P hP).asIdeal := dif_neg hP


@[simp] theorem mem_fibSet {n : ℤ} {Q P : (W⁄K).Point} : P ∈ fibSet W K n Q ↔ n • P = Q := Iff.rfl

open Classical in


theorem fibIdeal_eq {n : ℤ} {Q : (W⁄K).Point} (h : (fibSet W K n Q).Finite) :
    fibIdeal W K n Q = ∏ P ∈ h.toFinset, placeIdeal W K P := by
  rw [fibIdeal, dif_pos h]

open Classical in


theorem span_weilNum {n : ℤ} {T : (W⁄K).Point} (h : (fibIdeal W K n T).IsPrincipal) :
    Ideal.span {weilNum W K n T} = fibIdeal W K n T := by
  rw [weilNum, dif_pos h]
  exact @Ideal.span_singleton_generator _ _ _ h


theorem transEquiv_weilFun [IsAlgClosed K] [W.IsElliptic] {n : ℤ} {S T : (W⁄K).Point}
    (h : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (weilPairing0 W K n S T : K) * weilFun W K n T := by
  rw [weilPairing0, dif_pos h]
  exact h.choose_spec

theorem weilPairing0_of_not [IsAlgClosed K] [W.IsElliptic] {n : ℤ} {S T : (W⁄K).Point}
    (h : ¬ ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T) :
    weilPairing0 W K n S T = 1 := by
  rw [weilPairing0, dif_neg h]

end WeilPairingDefs
end WeierstrassCurve.Affine
