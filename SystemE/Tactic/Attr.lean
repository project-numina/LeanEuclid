import Lean

open Lean Meta Elab Command Simp

initialize euclidExtension : LabelExtension ← registerLabelAttr `euclid "System E inference axiom"

initialize diagExtension : LabelExtension ← registerLabelAttr `diag "System E diagrammatic inference axiom"
initialize metricExtension : LabelExtension ← registerLabelAttr `metric "System E metric inference axiom"
initialize superExtension : LabelExtension ← registerLabelAttr `super "System E superposition inference axiom"
initialize transferExtension : LabelExtension ← registerLabelAttr `transfer "System E transfer inference axiom"

def getEuclidTheorems : CoreM (Array Name) := do
  pure <| euclidExtension.getState (← getEnv)

elab "#euclid_post" : command => do
  liftTermElabM do
    IO.println "=== post simp theorems ==="
    for thm in  ← getEuclidTheorems do
      IO.println thm
