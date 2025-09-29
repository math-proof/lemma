import Mathlib.Tactic
open Lean

def filename : IO String := do
  let filename ← IO.Process.run {
    cmd := "sh",
    args := #["-c", "ps -o args= -p $PPID | awk '{print $3}'"],
  }
  return filename.trimRight


def lean2ilean (filePath : System.FilePath ) : System.FilePath :=
  ".lake/build/lib/lean" / filePath.withExtension "ilean"


def getFileMap (fileName : String) : IO FileMap :=
  -- make sure to replace \r\n with \n beforehand
  (·.toFileMap) <$> IO.FS.readFile fileName

def exec (fn : MetaM α) : IO α := do
  let env ← importModules #[{ module := `Mathlib.Tactic }] {}
  let ((result, _), _) ← Meta.MetaM.run fn |>.toIO
    -- Create a default Core.Context
    {
      fileName := "",
      fileMap := ⟨"", #[]⟩,
    }
    -- Create a default Core.State
    { env }
  return result
