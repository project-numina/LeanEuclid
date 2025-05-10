/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Qq

import SystemE.Theory.Sorts
import SystemE.Theory.Relations

import Smt.Translate
import Smt.Translate.Commands

open Smt
open Translate
open Qq
open Translator Term

#check Term

def listToArrow : List Term → Term
  | [s] => s
  | d::l => arrowT d (listToArrow l)
  | [] => default
-- | [] => default
-- def defNatSub : Command :=
--   .defineFun "Nat.sub" [("x", symbolT "Nat"), ("y", symbolT "Nat")] (symbolT "Nat")
--     (Term.mkApp3 (symbolT "ite")
--                  (Term.mkApp2 (symbolT "<") (symbolT "x") (symbolT "y"))
--                  (literalT "0")
--                  (Term.mkApp2 (symbolT "-") (symbolT "x") (symbolT "y")))
--     false

@[smt_translate] def translateEuclidType : Translator := fun (e : Q(Type)) => match e with
  | ~q(Point)  => return symbolT "Point"
  | ~q(Line)   => return symbolT "Line"
  | ~q(Circle)   => return symbolT "Circle"
  | ~q(Angle)    => return symbolT "Angle"
  | ~q(Segment) => return symbolT "Segment"
  | ~q(Triangle) => return symbolT "Triangle"
  | _         => return none

open Smt Command

def defineSort' (s : String) (l : List Term) (t : Term) : Command :=
  .declare s (listToArrow (l ++ [t]))

def euclidSorts : List Command := [
  .declareSort "Point" 0,
  .declareSort "Line" 0,
  .declareSort "Circle" 0,
  .declareSort "Angle" 0,
  .declareSort "Segment" 0,
  .declareSort "Triangle" 0,
  defineSort' "Angle.ofPoints" [symbolT "Point", symbolT "Point", symbolT "Point"] (symbolT "Angle"),
  defineSort' "Triangle.ofPoints" [symbolT "Point", symbolT "Point", symbolT "Point"] (symbolT "Triangle"),
  defineSort' "Segment.endpoints" [symbolT "Point", symbolT "Point"] (symbolT "Segment"),
  defineSort' "Angle.degree" [symbolT "Angle"] (symbolT "Real"),
  .declare "Angle.Right" (symbolT "Real"),
  defineSort' "Segment.length" [symbolT "Segment"] (symbolT "Real"),
  defineSort' "Triangle.area" [symbolT "Triangle"] (symbolT "Real"),
  defineSort' "Point.onLine" [symbolT "Point", symbolT "Line"] (symbolT "Bool"),
  defineSort' "Point.sameSide" [symbolT "Point", symbolT "Point", symbolT "Line"] (symbolT "Bool"),
  defineSort' "collinear" [symbolT "Point", symbolT "Point", symbolT "Point"] (symbolT "Bool"),
  defineSort' "between" [symbolT "Point", symbolT "Point", symbolT "Point"] (symbolT "Bool"),
  defineSort' "Point.onCircle" [symbolT "Point", symbolT "Circle"] (symbolT "Bool"),
  defineSort' "Point.insideCircle" [symbolT "Point", symbolT "Circle"] (symbolT "Bool"),
  defineSort' "Point.isCentre" [symbolT "Point", symbolT "Circle"] (symbolT "Bool"),
  defineSort' "Line.intersectsLine" [symbolT "Line", symbolT "Line"] (symbolT "Bool"),
  defineSort' "Line.intersectsCircle" [symbolT "Line", symbolT "Circle"] (symbolT "Bool"),
  defineSort' "Circle.intersectsCircle" [symbolT "Circle", symbolT "Circle"] (symbolT "Bool"),
]

open Lean

/-
  translate function and predicate constants
-/
-- todo automate this with a reserved sort attribute
@[smt_translate] def translateFun : Translator := fun (e : Expr) =>
  match e with
  | (Expr.const `Angle.ofPoints _) => return (symbolT "Angle.ofPoints")
  | Expr.const `Triangle.ofPoints _ => return (symbolT "Triangle.ofPoints")
  | (Expr.const `Segment.endpoints _) => return (symbolT "Segment.endpoints")
  | Expr.const `Angle.degree _ => return symbolT "Angle.degree"
  | Expr.const `Angle.Right _ => return symbolT "Angle.Right"
  | Expr.const `Segment.length _ => return symbolT "Segment.length"
  | Expr.const `Triangle.area _ => return symbolT "Triangle.area"
  | Expr.const `Point.onLine _ => return symbolT "Point.onLine"
  | (Expr.const `Point.sameSide _) => return (symbolT "Point.sameSide")
  | Expr.const `collinear _ => return symbolT "collinear"
  | Expr.const `between _ => return symbolT "between"
  | Expr.const `Point.onCircle _ => return symbolT "Point.onCircle"
  | Expr.const `Point.insideCircle _ => return symbolT "Point.insideCircle"
  | Expr.const `Point.isCentre _ => return symbolT "Point.isCentre"
  | Expr.const `Line.intersectsLine _ => return symbolT "Line.intersectsLine"
  | Expr.const `Line.intersectsCircle _ => return symbolT "Line.intersectsCircle"
  | Expr.const `Circle.intersectsCircle _ => return symbolT "Circle.intersectsCircle"
  | _ => return none
