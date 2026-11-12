# Lemma rename workflow

- Rename a py lemma using `sh/rename.sh`.
- Execute `ps1/run.ps1`, fixing errors if necessary. Do not modify the given, imply, or proof body. The result should be like:

  proved = 4043
  total = 4291
  failed = 0
  plausible = 0

- Open the summary at http://localhost:8080/py/ and check that the unformalized list is empty. If it is not empty, some paths might have been neglected in a rename; repeat the previous steps.
- `git add .`, commit, and push.
