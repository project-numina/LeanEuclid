import Lean

import Smt.Tactic.Smt
import SystemE.Tactic.Attr

namespace Smt

open Lean hiding Command
open Elab Tactic Qq
open Smt Translate Query Reconstruct Util

namespace Tactic

syntax (name := esmt) "esmt" smtHints smtTimeout : tactic

#check Expr.isProp
/-
  if no hints are given the entire local context is used
-/
@[tactic esmt]
def evalESmt : Tactic := fun stx => withMainContext do
  let axioms := euclidExtension.getState (← getEnv)
  let axiomExprs : List Expr := (← axioms.toList.mapM (fun x => do
    let e ← `(show _ from $(mkIdent x))
    elabTerm e none
  ))

  let userHints ← parseHints ⟨stx[1]⟩

  -- If hints are empty, fall back to all local declarations
  let hints ← if userHints.isEmpty then
    let lctx ← getLCtx
    lctx.foldlM (init := []) fun acc decl =>
      if decl.isImplementationDetail || decl.isAuxDecl then
        pure acc
      else do
        -- let type ← instantiateMVars decl.type
        if ← Meta.isProp decl.type then
          pure (acc.concat decl.toExpr)
        else
          pure acc
  else
    pure userHints

  let mvs ← Smt.smt (← Tactic.getMainGoal) (axiomExprs ++ hints) (← parseTimeout ⟨stx[2]⟩)
  Tactic.replaceMainGoal mvs
