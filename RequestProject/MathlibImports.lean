module

public import Mathlib.Tactic.ApplyFun
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.Zify
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
Shared Mathlib imports for the rc3 migration. Importing the complete Mathlib
umbrella exhausted the local Windows loader's memory when several sources were
checked at once. This module changes the imported library surface only; it adds
no mathematical declarations or axioms.
-/
