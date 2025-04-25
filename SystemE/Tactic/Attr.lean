import Lean

open Lean Meta Elab Command Simp

initialize euclidExtension : LabelExtension ← registerLabelAttr `euclid "System E inference axiom"

def getEuclidTheorems : CoreM (Array Name) := do
  pure <| euclidExtension.getState (← getEnv)

/--
`pwFilter R l` is a maximal sublist of `l` which is `Pairwise R`.
`pwFilter (·≠·)` is the erase duplicates function (cf. `eraseDup`), and `pwFilter (·<·)` finds
a maximal increasing subsequence in `l`. For example,
```
pwFilter (·<·) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4]
```
-/
def pwFilter (R : α → α → Prop) [DecidableRel R] (l : List α) : List α :=
  l.foldr (fun x IH => if ∀ y ∈ IH, R x y then x :: IH else IH) []

/-- `dedup l` removes duplicates from `l` (taking only the last occurrence).
  Defined as `pwFilter (≠)`.

     dedup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def List.dedup [DecidableEq α] : List α → List α :=
  pwFilter (· ≠ ·)

elab "#euclid_post" : command => do
  liftTermElabM do
    IO.println "=== post simp theorems ==="
    for thm in  ← getEuclidTheorems do
      IO.println thm
