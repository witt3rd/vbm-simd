import Lean
import VbmSimd
import VbmSimdProofs
/-! Axiom gate (Tier 1 here: the library is small, so it is cheap): every constant defined in a `VbmSimd` or `VbmSimdProofs` module may depend only
on the three standard axioms. Exits non-zero (and names the offenders) otherwise. `--selftest` also proves the gate can fail: a
synthetic constant that declares a non-standard axiom is added to the environment, and the audit must reject it. -/
open Lean

def allowed : List Name := [`propext, `Classical.choice, `Quot.sound]

def audit (names : Array Name) : CoreM (Nat × Nat) := do
  let mut bad := 0
  for n in names do
    for a in (← collectAxioms n) do
      unless allowed.contains a do
        IO.eprintln s!"{n} depends on non-standard axiom {a}"
        bad := bad + 1
  return (names.size, bad)

def ours (r : Name) : Bool := r == `VbmSimd || r == `VbmSimdProofs

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `VbmSimd }, { module := `VbmSimdProofs }] {}
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if ours (env.header.moduleNames[idx.toNat]!).getRoot then names := names.push n
  let ((count, bad), _) ← (audit names).toIO { fileName := "", fileMap := default } { env }
  IO.println s!"axiom gate: {count} constants checked, {bad} offending"
  if args.contains "--selftest" then
    let selfTest : CoreM (Nat × Nat) := do
      addDecl (.axiomDecl { name := `selftest.bad, levelParams := [], type := mkConst ``False, isUnsafe := false })
      audit #[`selftest.bad]
    let (out, ((_, selfBad), _)) ← IO.FS.withIsolatedStreams (selfTest.toIO { fileName := "", fileMap := default } { env })
    if selfBad == 0 then IO.eprintln s!"tier1: the axiom gate cannot fail (it accepted a non-standard axiom){out}"; return 1
    IO.println "axiom gate: negative self-test ok (a constant on a non-standard axiom is rejected)"
  return if bad == 0 then 0 else 1
