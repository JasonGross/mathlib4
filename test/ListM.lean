/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic
import Mathlib.Data.ListM.Parallel
import Mathlib.Control.Basic

@[reducible] def S (α : Type) := StateT (List Nat) Option α
def append (x : Nat) : S Unit :=
  fun s => some ((), x :: s)

def F : Nat → S Nat
  | 0 => failure
  | (n+1) => do
      append (n+1)
      pure n

open Lean

#eval show MetaM Unit from do
  -- Note that `fix` fails if any invocation of `F` fails.
  -- This is different from previous behaviour, where it just terminated the lazy list.
  -- Hence we must use `.takeAsList 11` here rather than `.force`.
  let x := ((ListM.fix F 10).takeAsList 11).run []
  guard $ x = some ([10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

example : ((ListM.fix F 10).takeAsList 4).run [] = some ([10, 9, 8, 7], [8, 9, 10]) := by
  native_decide
example :
    (((ListM.fix F 10).map fun n => n*n).takeAsList 3).run [] =
      some ([100, 81, 64], [9, 10]) := by
  native_decide

def l1 : ListM S Nat := ListM.ofList [0,1,2]
def l2 : ListM S Nat := ListM.ofList [3,4,5]
def ll : ListM S Nat := (ListM.ofList [l1, l2]).join

#eval show MetaM Unit from do
  let x := ll.force.run []
  guard $ x = some ([0, 1, 2, 3, 4, 5], [])

def half_or_fail (n : Nat) : MetaM Nat :=
do guard (n % 2 = 0)
   pure (n / 2)

#eval do
  let x : ListM MetaM Nat := ListM.range
  let y := x.filterMapM fun n => try? <| half_or_fail n
  let z ← y.takeAsList 10
  guard $ z.length = 10

#eval do
  let R : ListM MetaM Nat := ListM.range
  let S : ListM MetaM Nat := R.filterMapM fun n => try? do
    guard (n % 5 = 0)
    pure n
  let n ← R.takeAsList 5
  let m ← S.head
  guard $ n = [0,1,2,3,4]
  guard $ m = 0

#eval do
  let R : ListM MetaM Nat := ListM.range
  let n ← R.firstM fun n => try? do
    guard (n = 5)
    pure n
  guard $ n = 5

partial def collatz (n : Nat) : Nat :=
  go 0 n
where go (s n : Nat) :=
  if n ≤ 1 then
    s
  else
    go (s+1) (if n % 2 = 0 then n / 2 else 3 * n + 1)

-- set_option profiler true in -- around 8.3s
-- #eval do
--   let R : ListM MetaM Nat := ListM.range |>.parallelMap collatz (chunkSize := 1000)
--   _ ← R.takeAsArray 1000000

-- set_option profiler true in -- around 77s
-- #eval do
--   let R : ListM MetaM Nat := ListM.range |>.map collatz
--   _ ← R.takeAsArray 1000000
