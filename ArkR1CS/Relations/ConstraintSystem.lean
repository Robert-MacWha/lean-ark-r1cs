/-
# `ark_relations::gr1cs::ConstraintSystem`

A gadget is a function of the constraint system it synthesises into. Here the
constraint system is represented by its allocation counters (`Counters`,
threaded like a `ConstraintSystemRef`) and the list of operations the gadget
performs on it (`Op`): allocating an instance variable, allocating a witness
variable, or enforcing one R1CS row. `CS F α` is the resulting monad.

Soundness is stated against *arbitrary* assignments (`ConstraintsHold`): no
assumption is made about how the prover produced them. The honest
assignment (`honestAssignment`) is only used by the executable
`isSatisfied` check and by `ArkR1CS.Trace`.
-/
import ArkR1CS.Relations.Variable
import Mathlib.Logic.Function.Basic

namespace ArkR1CS

variable {F : Type}

/-- One R1CS row `a * b = c` (one predicate constraint of the `R1CS` label). -/
structure Constraint (F : Type) where
  a : LinearCombination F
  b : LinearCombination F
  c : LinearCombination F
  deriving Repr

/-- The row is satisfied by `x`. -/
def Constraint.holds [Field F] (x : Assignment F) (k : Constraint F) : Prop :=
  k.a.eval x * k.b.eval x = k.c.eval x

/-- A side effect on the constraint system. The value carried by `input` /
`witness` is what the allocation closure returns in proving mode. -/
inductive Op (F : Type)
  | input (val : F)
  | witness (val : F)
  | constrain (k : Constraint F)
  deriving Repr

namespace Op

/-- Number of instance variables allocated. -/
def inputCount : List (Op F) → Nat
  | [] => 0
  | .input _ :: rest => inputCount rest + 1
  | .witness _ :: rest => inputCount rest
  | .constrain _ :: rest => inputCount rest

/-- Number of witness variables allocated. -/
def witnessCount : List (Op F) → Nat
  | [] => 0
  | .input _ :: rest => witnessCount rest
  | .witness _ :: rest => witnessCount rest + 1
  | .constrain _ :: rest => witnessCount rest

/-- The R1CS rows, in order. -/
def constraints : List (Op F) → List (Constraint F)
  | [] => []
  | .input _ :: rest => constraints rest
  | .witness _ :: rest => constraints rest
  | .constrain k :: rest => k :: constraints rest

theorem inputCount_append (l₁ l₂ : List (Op F)) :
    inputCount (l₁ ++ l₂) = inputCount l₁ + inputCount l₂ := by
  induction l₁ with
  | nil => simp [inputCount]
  | cons op rest ih => cases op <;> simp [inputCount, ih, Nat.add_right_comm]

theorem witnessCount_append (l₁ l₂ : List (Op F)) :
    witnessCount (l₁ ++ l₂) = witnessCount l₁ + witnessCount l₂ := by
  induction l₁ with
  | nil => simp [witnessCount]
  | cons op rest ih => cases op <;> simp [witnessCount, ih, Nat.add_right_comm]

theorem constraints_append (l₁ l₂ : List (Op F)) :
    constraints (l₁ ++ l₂) = constraints l₁ ++ constraints l₂ := by
  induction l₁ with
  | nil => rfl
  | cons op rest ih => cases op <;> simp [constraints, ih]

end Op

/-- `num_instance_variables` / `num_witness_variables`. -/
@[ext]
structure Counters where
  num_instance_variables : Nat
  num_witness_variables : Nat
  deriving DecidableEq, Repr

/-- `ConstraintSystem::new()`: the constant one is instance variable 0. -/
def Counters.new : Counters := ⟨1, 0⟩

/-- Counters after performing `ops`. -/
def Counters.advance (c : Counters) (ops : List (Op F)) : Counters :=
  ⟨c.num_instance_variables + Op.inputCount ops, c.num_witness_variables + Op.witnessCount ops⟩

@[simp] theorem Counters.advance_nil (c : Counters) : c.advance ([] : List (Op F)) = c := by
  simp [Counters.advance, Op.inputCount, Op.witnessCount]

theorem Counters.advance_append (c : Counters) (l₁ l₂ : List (Op F)) :
    c.advance (l₁ ++ l₂) = (c.advance l₁).advance l₂ := by
  simp [Counters.advance, Op.inputCount_append, Op.witnessCount_append, Nat.add_assoc]

@[simp] theorem Counters.advance_num_instance_variables (c : Counters) (ops : List (Op F)) :
    (c.advance ops).num_instance_variables = c.num_instance_variables + Op.inputCount ops := rfl

@[simp] theorem Counters.advance_num_witness_variables (c : Counters) (ops : List (Op F)) :
    (c.advance ops).num_witness_variables = c.num_witness_variables + Op.witnessCount ops := rfl

/-! ### Gadgets as computations on the constraint system -/

/-- A gadget: given the current counters, its output and the operations it
performs. `bind` threads the counters like a `ConstraintSystemRef`. -/
structure CS (F : Type) (α : Type) where
  run : Counters → α × List (Op F)

namespace CS

variable {α β : Type}

protected def pure (x : α) : CS F α := ⟨fun _ => (x, [])⟩

protected def bind (c : CS F α) (f : α → CS F β) : CS F β :=
  ⟨fun k =>
    (((f (c.run k).1).run (k.advance (c.run k).2)).1,
      (c.run k).2 ++ ((f (c.run k).1).run (k.advance (c.run k).2)).2)⟩

instance : Monad (CS F) where
  pure := CS.pure
  bind := CS.bind

@[simp] theorem run_pure (x : α) (k : Counters) : (pure x : CS F α).run k = (x, []) := rfl

@[simp] theorem run_bind (c : CS F α) (f : α → CS F β) (k : Counters) :
    (c >>= f).run k =
      (((f (c.run k).1).run (k.advance (c.run k).2)).1,
        (c.run k).2 ++ ((f (c.run k).1).run (k.advance (c.run k).2)).2) := rfl

end CS

/-- `ConstraintSystemRef::new_input_variable`. -/
def new_input_variable (v : F) : CS F Variable :=
  ⟨fun k => (.Instance k.num_instance_variables, [.input v])⟩

/-- `ConstraintSystemRef::new_witness_variable`. -/
def new_witness_variable (v : F) : CS F Variable :=
  ⟨fun k => (.Witness k.num_witness_variables, [.witness v])⟩

/-- `ConstraintSystemRef::new_lc`: symbolic linear combinations are inlined,
so this allocates nothing. -/
def new_lc (lc : LinearCombination F) : CS F (LinearCombination F) := pure lc

/-- `ConstraintSystemRef::enforce_r1cs_constraint`. -/
def enforce_r1cs_constraint (a b c : LinearCombination F) : CS F Unit :=
  ⟨fun _ => ((), [.constrain ⟨a, b, c⟩])⟩

@[simp] theorem run_new_input_variable (v : F) (k : Counters) :
    (new_input_variable v).run k = (.Instance k.num_instance_variables, [.input v]) := rfl

@[simp] theorem run_new_witness_variable (v : F) (k : Counters) :
    (new_witness_variable v).run k = (.Witness k.num_witness_variables, [.witness v]) := rfl

@[simp] theorem run_new_lc (lc : LinearCombination F) (k : Counters) :
    (new_lc lc).run k = (lc, []) := rfl

@[simp] theorem run_enforce_r1cs_constraint (a b c : LinearCombination F) (k : Counters) :
    (enforce_r1cs_constraint a b c).run k = ((), [.constrain ⟨a, b, c⟩]) := rfl

/-! ### Satisfaction by an arbitrary assignment -/

/-- Every row contributed by `ops` is satisfied by `a`. -/
def ConstraintsHold [Field F] (a : Assignment F) (ops : List (Op F)) : Prop :=
  ∀ k ∈ Op.constraints ops, k.holds a

section
variable [Field F]

@[simp] theorem constraintsHold_nil (a : Assignment F) : ConstraintsHold a ([] : List (Op F)) := by
  simp [ConstraintsHold, Op.constraints]

@[simp] theorem constraintsHold_input (a : Assignment F) (v : F) (rest : List (Op F)) :
    ConstraintsHold a (.input v :: rest) ↔ ConstraintsHold a rest := Iff.rfl

@[simp] theorem constraintsHold_witness (a : Assignment F) (v : F) (rest : List (Op F)) :
    ConstraintsHold a (.witness v :: rest) ↔ ConstraintsHold a rest := Iff.rfl

@[simp] theorem constraintsHold_constrain (a : Assignment F) (k : Constraint F)
    (rest : List (Op F)) :
    ConstraintsHold a (.constrain k :: rest) ↔ k.holds a ∧ ConstraintsHold a rest := by
  simp [ConstraintsHold, Op.constraints]

@[simp] theorem constraintsHold_append (a : Assignment F) (l₁ l₂ : List (Op F)) :
    ConstraintsHold a (l₁ ++ l₂) ↔ ConstraintsHold a l₁ ∧ ConstraintsHold a l₂ := by
  simp [ConstraintsHold, Op.constraints_append, or_imp, forall_and]

end

/-! ### The honest assignment (executable checks only) -/

/-- Overwrite the `i`-th instance variable. -/
def Assignment.setInstance (a : Assignment F) (i : Nat) (v : F) : Assignment F :=
  { a with instance_assignment := Function.update a.instance_assignment i v }

/-- Overwrite the `i`-th witness variable. -/
def Assignment.setWitness (a : Assignment F) (i : Nat) (v : F) : Assignment F :=
  { a with witness_assignment := Function.update a.witness_assignment i v }

/-- The assignment the prover builds while synthesising: every allocated
variable receives the value its allocation closure returned. -/
def extend (k : Counters) (a : Assignment F) : List (Op F) → Assignment F
  | [] => a
  | .input v :: rest =>
    extend ⟨k.num_instance_variables + 1, k.num_witness_variables⟩
      (a.setInstance k.num_instance_variables v) rest
  | .witness v :: rest =>
    extend ⟨k.num_instance_variables, k.num_witness_variables + 1⟩
      (a.setWitness k.num_witness_variables v) rest
  | .constrain _ :: rest => extend k a rest

/-- The prover's assignment for a gadget run from a fresh constraint system. -/
def honestAssignment [Field F] (ops : List (Op F)) : Assignment F :=
  extend Counters.new ⟨fun _ => 0, fun _ => 0⟩ ops

/-- `ConstraintSystemRef::is_satisfied` for the prover's own assignment. -/
def isSatisfied [Field F] [DecidableEq F] (ops : List (Op F)) : Bool :=
  let a := honestAssignment ops
  (Op.constraints ops).all fun k => decide (k.a.eval a * k.b.eval a = k.c.eval a)

end ArkR1CS
