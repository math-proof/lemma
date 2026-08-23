"""One-at-a-time Algebra.Eq* moves. Stop on first failure."""
import subprocess
import sys

PAIRS = [
    ("Algebra.EqMul.of.Eq.Lt", "Nat.EqMul.of.Eq.Lt"),
    ("Algebra.EqMul.of.Gt_0.Eq", "Nat.EqMul.of.Gt_0.Eq"),
    ("Algebra.EqNeg.of.Eq", "Int.EqNeg.of.Eq"),
    ("Algebra.EqNorm.of.Eq", "Real.EqNorm.of.Eq"),
    ("Algebra.EqPow.of.Eq_even", "Nat.EqPow.of.Eq_even"),
    ("Algebra.EqPow.of.Eq_odd", "Nat.EqPow.of.Eq_odd"),
    ("Algebra.EqProd.of.Eq.Eq.push", "Finset.EqProd.of.Eq.Eq.push"),
    ("Algebra.EqProd.of.Eq.Eq.unshift", "Finset.EqProd.of.Eq.Eq.unshift"),
    ("Algebra.EqProd.of.All_Eq", "Finset.EqProd.of.All_Eq"),
    ("Algebra.EqProd.of.Eq", "Finset.EqProd.of.Eq"),
    ("Algebra.EqRe.of.Eq", "Complex.EqRe.of.Eq"),
    ("Algebra.EqReducedArgMax.of.Eq", "Tensor.EqReducedArgMax.of.Eq"),
    ("Algebra.EqReducedArgMin.of.Eq", "Tensor.EqReducedArgMin.of.Eq"),
    ("Algebra.EqReducedMax.of.Eq", "Tensor.EqReducedMax.of.Eq"),
    ("Algebra.EqReducedMin.of.Eq", "Tensor.EqReducedMin.of.Eq"),
    ("Algebra.EqReducedSum.of.Eq", "Tensor.EqReducedSum.of.Eq"),
    ("Algebra.EqSign.of.Gt_0", "Int.EqSign.of.Gt_0"),
    ("Algebra.EqSign.of.Lt_0", "Int.EqSign.of.Lt_0"),
    ("Algebra.EqSlice.of.Le.Eq", "Tensor.EqSlice.of.Le.Eq"),
    ("Algebra.EqSqrt.of.Eq", "Real.EqSqrt.of.Eq"),
    ("Algebra.EqSquare.of.Ne_0.Add.eq.Zero", "Real.EqSquare.of.Ne_0.Add.eq.Zero"),
    ("Algebra.EqSub.of.Eq.Eq", "Int.EqSub.of.Eq.Eq"),
    ("Algebra.EqSup.of.Lt", "Real.EqSup.of.Lt"),
    ("Algebra.EqSup.of.Eq", "Real.EqSup.of.Eq"),
    ("Algebra.EqTranspose.of.Eq", "Tensor.EqTranspose.of.Eq"),
    ("Algebra.Eq_0.Delta.Mul.of.Ne", "Nat.Eq_0.Delta.Mul.of.Ne"),
    ("Algebra.Eq_0.Delta.of.Ne", "Nat.Eq_0.Delta.of.Ne"),
    ("Algebra.Eq_0.Is.Cond.invert", "Bool.Eq_0.Is.Cond.invert"),
    ("Algebra.Eq_0.Min.of.Ge_0", "Nat.Eq_0.Min.of.Ge_0"),
    ("Algebra.Eq_0.Sum.Sub.of.Eq_ReducedSum", "Tensor.Eq_0.Sum.Sub.of.Eq_ReducedSum"),
    ("Algebra.Eq_0.given.Cond.invert", "Bool.Eq_0.given.Cond.invert"),
    ("Algebra.Eq_0.given.Eq", "Int.Eq_0.given.Eq"),
    ("Algebra.Eq_0.of.Abs.le.Zero", "Int.Eq_0.of.Abs.le.Zero"),
    ("Algebra.Eq_0.of.Eq", "Tensor.Eq_0.of.Eq"),
    ("Algebra.Eq_0.of.Ge_0", "Nat.Eq_0.of.Ge_0"),
    ("Algebra.Eq_Bool.Is.Cond", "Bool.Eq_Bool.Is.Cond"),
    ("Algebra.Eq_Ceil.given.And", "Int.Eq_Ceil.given.And"),
    ("Algebra.Eq_Ite.given.Eq.Block", "Tensor.Eq_Ite.given.Eq.Block"),
    ("Algebra.Eq_Ite.of.Cond", "Bool.Eq_Ite.of.Cond"),
    ("Algebra.Eq_Max.given.Ge", "Nat.Eq_Max.given.Ge"),
    ("Algebra.Eq_Max.given.Le", "Nat.Eq_Max.given.Le"),
    ("Algebra.Eq_Min.given.Le", "Nat.Eq_Min.given.Le"),
    ("Algebra.Eq_Min.given.Ge", "Nat.Eq_Min.given.Ge"),
    ("Algebra.Eq_even.of.Ne", "Nat.Eq_even.of.Ne"),
    ("Algebra.Eq_even.of.Ne_1", "Nat.Eq_even.of.Ne_1"),
    ("Algebra.Eq_even.given.Any", "Nat.Eq_even.given.Any"),
    ("Algebra.Eq_even.given.Eq", "Nat.Eq_even.given.Eq"),
    ("Algebra.Eq_odd.given.Eq", "Nat.Eq_odd.given.Eq"),
    ("Algebra.Eq_even.Is.Eq", "Nat.Eq_even.Is.Eq"),
    ("Algebra.Eq_odd.Is.Eq", "Nat.Eq_odd.Is.Eq"),
    ("Algebra.Eq_odd.Is.Ne.Zero", "Nat.Eq_odd.Is.Ne.Zero"),
]


def main():
    start = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    for i, (src, dst) in enumerate(PAIRS[start:], start=start):
        print(f"\n======== [{i + 1}/{len(PAIRS)}] {src} -> {dst} ========", flush=True)
        env = __import__("os").environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        r = subprocess.run(
            [sys.executable, "util/rename_algebra.py", src, dst, "--prove"],
            cwd=r"e:\github\py",
            text=True,
            capture_output=True,
            encoding="utf-8",
            errors="replace",
            env=env,
        )
        out = (r.stdout or "") + (r.stderr or "")
        print(out, end="", flush=True)
        if f"{src} -> {dst}" not in out or "total failed    = 0" not in out:
            print(f"STOP at {src}: rename/prove failed, exit {r.returncode}", flush=True)
            sys.exit(2)
    print("ALL_EQ_DONE", flush=True)


if __name__ == "__main__":
    main()
