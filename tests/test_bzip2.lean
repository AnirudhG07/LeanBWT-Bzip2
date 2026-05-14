/-
This file contains common helper functions which serve as testing framework for the Bzip2 test suite.
-/

import Bzip2

structure Summary where
  passed : Nat := 0
  failed : Nat := 0
  skipped : Nat := 0
deriving Repr

inductive TestOutcome where
  | pass
  | fail (message : String)
  | skip (reason : String)
deriving Repr

structure TestCase where
  name : String
  run : IO TestOutcome

def runCase (summary : Summary) (tc : TestCase) : IO Summary := do
  match ← tc.run with
  | .pass =>
      IO.println s!"PASS {tc.name}"
      pure { summary with passed := summary.passed + 1 }
  | .fail message =>
      IO.println s!"FAIL {tc.name}: {message}"
      pure { summary with failed := summary.failed + 1 }
  | .skip reason =>
      IO.println s!"SKIP {tc.name}: {reason}"
      pure { summary with skipped := summary.skipped + 1 }

def runCases : Summary → List TestCase → IO Summary
  | summary, [] => pure summary
  | summary, tc :: rest => do
      let summary' ← runCase summary tc
      runCases summary' rest

/-

-- Put all your tests here
private def allCases : List TestCase :=
  smallCases ++ mediumCases ++ streamCases ++ negativeCases ++ exactBz2Cases

-- Run all the tests and print a summary
def main : IO Unit := do
  let summary ← runCases {} allCases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} exact `.bz2` test(s) failed."
-/

/-
## Helper Functions for tests
-/

def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else if 'A' ≤ c ∧ c ≤ 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else
    none

def decodeHexAux : List Char → List UInt8 → Except String ByteArray
  | [], acc => .ok <| ByteArray.mk acc.reverse.toArray
  | [_], _ => .error "Fixture hex has odd length."
  | hi :: lo :: rest, acc =>
      match hexValue? hi, hexValue? lo with
      | some hiVal, some loVal =>
          decodeHexAux rest (UInt8.ofNat (hiVal * 16 + loVal) :: acc)
      | _, _ => .error "Fixture hex contains a non-hex character."

def loadFixture (name : String) : IO (Except String ByteArray) := do
  let path : System.FilePath := s!"tests/fixtures/bz2/{name}"
  let raw ← IO.FS.readFile path
  let hexChars := raw.toList.filter (fun c => hexValue? c |>.isSome)
  pure <| decodeHexAux hexChars []

def byteArrayOfList (xs : List UInt8) : ByteArray :=
  ByteArray.mk xs.toArray

def appendByteArray (left right : ByteArray) : ByteArray :=
  right.foldl ByteArray.push left

def replaceByteAtAux : List UInt8 → Nat → UInt8 → List UInt8
  | [], _, _ => []
  | _ :: rest, 0, value => value :: rest
  | byte :: rest, index + 1, value => byte :: replaceByteAtAux rest index value

def replaceByteAt (bytes : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  byteArrayOfList <| replaceByteAtAux bytes.toList index value

def removeIfExists (path : System.FilePath) : IO Unit := do
  if (← path.pathExists) then
    IO.FS.removeFile path

def shellCommandPath? (name : String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "bash", args := #["-lc", s!"command -v {name}"] }
  if out.exitCode = 0 then
    pure (some out.stdout.trimAscii.toString)
  else
    pure none

def requireShellBzip2 (action : IO TestOutcome) : IO TestOutcome := do
  match ← shellCommandPath? "bzip2" with
  | none => pure <| .skip "shell command `bzip2` is not available on this machine"
  | some _ => action

def runSystemBzip2 (args : Array String) : IO (Except String Unit) := do
  let out ← IO.Process.output { cmd := "bzip2", args := args }
  if out.exitCode = 0 then
    pure (.ok ())
  else
    pure (.error s!"exit {out.exitCode}: {out.stderr}")

def runSystemBunzip2 (args : Array String) : IO (Except String Unit) := do
  let out ← IO.Process.output { cmd := "bunzip2", args := args }
  if out.exitCode = 0 then
    pure (.ok ())
  else
    pure (.error s!"exit {out.exitCode}: {out.stderr}")
