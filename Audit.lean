import SchurEntropy
import Mathlib.Util.AssertNoSorry

/-! Reject any transitive axiom other than Lean's standard foundations for
every declaration in the imported `SchurEntropy` namespace. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (`SchurEntropy).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "{name} depends on disallowed axiom {ax}"
      count := count + 1
  logInfo m!"Audited {count} SchurEntropy declarations: only standard foundational axioms."

#print axioms SchurEntropy.optimizedConcavity
#print axioms SchurEntropy.scalar_joint_convexity
#print axioms SchurEntropy.block_entropy_inequality

example : SchurEntropy.OptimizedConcavityStatement := SchurEntropy.optimizedConcavity
example : SchurEntropy.ScalarConvexityStatement := SchurEntropy.scalar_joint_convexity
example : SchurEntropy.BlockEntropyStatement := SchurEntropy.block_entropy_inequality
