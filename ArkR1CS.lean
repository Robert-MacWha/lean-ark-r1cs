/-
# ArkR1CS

A Lean 4 model of `ark-relations` and `ark-r1cs-std`, mirrored module by
module, with soundness lemmas for every gadget: whatever assignment satisfies
the constraints a gadget emits, its output evaluates to the specified value.

* `ArkR1CS.Relations.*`        ↔ `ark_relations::gr1cs`
* `ArkR1CS.R1csStd.*`          ↔ `ark_r1cs_std`
* `ArkR1CS.CryptoPrimitives.*` ↔ `ark_crypto_primitives` (black-box interfaces)
* `ArkR1CS.Trace`              — canonical rendering for differential tests
-/
import ArkR1CS.Relations.Variable
import ArkR1CS.Relations.ConstraintSystem
import ArkR1CS.R1csStd.Boolean
import ArkR1CS.R1csStd.Eq
import ArkR1CS.R1csStd.Fields.Fp
import ArkR1CS.CryptoPrimitives.Crh
import ArkR1CS.Trace
