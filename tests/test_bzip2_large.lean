import Bzip2
import tests.test_bzip2

/-!
Dedicated large-file test harness.

These cases are kept separate from the main suite so routine development stays
fast and focused. Today they remain intentionally skipped because the current
exact encoder still uses the matrix/rotation-based BWT path, which is not yet
appropriate for multi-megabyte execution.

Once the native block sorter lands, this file is the right place to activate
the larger interoperability and stress tests.
-/

set_option autoImplicit false

private def pendingCase (name reason : String) : TestCase :=
  { name := name
  , run := pure (.skip reason)
  }

private def cases : List TestCase :=
  [ pendingCase "multi-megabyte text"
      "Current exact encoder still uses the matrix-based BWT path; activate after the native block sorter lands."
  , pendingCase "multi-megabyte binary"
      "Current exact encoder still uses the matrix-based BWT path; activate after the native block sorter lands."
  , pendingCase "highly repetitive large file"
      "Activate after the native block implementation replaces the spec-layer matrix algorithm."
  , pendingCase "incompressible large file"
      "Activate after the native block implementation replaces the spec-layer matrix algorithm."
  , pendingCase "files spanning many large blocks"
      "Activate after the native block implementation replaces the spec-layer matrix algorithm."
  ]


def main : IO Unit := do
  let summary ← runCases {} cases
  IO.println s!"\nSummary: {summary.passed} passed, {summary.failed} failed, {summary.skipped} skipped"
  if summary.failed ≠ 0 then
    throw <| IO.userError s!"{summary.failed} large-file test(s) failed."
