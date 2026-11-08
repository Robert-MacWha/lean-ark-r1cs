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

namespace ArkR1CS

variable {F : Type}

/-- Models one row `a * b = c` of the R1CS predicate (`R1CS_PREDICATE_LABEL`) in
`ark_relations::gr1cs::ConstraintSystem`. -/
structure Constraint (F : Type) where
  a : LinearCombination F
  b : LinearCombination F
  c : LinearCombination F
  deriving Repr

/-- The row `a * b = c` is satisfied by assignment `x`. No arkworks counterpart;
`ConstraintSystem::is_satisfied` checks this for the prover's own assignment. -/
def Constraint.holds [Field F] (x : Assignment F) (k : Constraint F) : Prop :=
  k.a.eval x * k.b.eval x = k.c.eval x

/-- One side effect of a gadget on the constraint system:
`ConstraintSystemRef::new_input_variable`, `new_witness_variable` or `enforce_r1cs_constraint`.
The value of an `input`/`witness` is what the allocation closure returned. No arkworks
counterpart. -/
inductive Op (F : Type)
  | input (val : F)
  | witness (val : F)
  | constrain (k : Constraint F)
  deriving Repr

namespace Op

/-- The value allocated by an `input` op. -/
@[cs_run] def input? : Op F → Option F
  | .input v => some v
  | _ => none

/-- The value allocated by a `witness` op. -/
@[cs_run] def witness? : Op F → Option F
  | .witness v => some v
  | _ => none

/-- The row enforced by a `constrain` op. -/
@[cs_run] def constraint? : Op F → Option (Constraint F)
  | .constrain k => some k
  | _ => none

/-- The values of the instance variables `ops` allocates, in order
(`ConstraintSystem::instance_assignment` without the leading one). -/
def inputs (ops : List (Op F)) : List F := ops.filterMap input?

/-- The values of the witness variables `ops` allocates, in order
(`ConstraintSystem::witness_assignment`). -/
def witnesses (ops : List (Op F)) : List F := ops.filterMap witness?

/-- The R1CS rows `ops` enforces, in order. -/
def constraints (ops : List (Op F)) : List (Constraint F) := ops.filterMap constraint?

end Op

/-- Models `ConstraintSystem::num_instance_variables` and `num_witness_variables`: the indices
the next allocations will get. -/
@[ext]
structure Counters where
  num_instance_variables : Nat
  num_witness_variables : Nat
  deriving DecidableEq, Repr

/-- Models `ConstraintSystem::new()`: no witnesses, and one instance variable (the constant one). -/
def Counters.new : Counters := ⟨1, 0⟩

/-- The counters after allocating the variables in `ops`. No arkworks counterpart. -/
def Counters.advance (c : Counters) (ops : List (Op F)) : Counters :=
  ⟨c.num_instance_variables + (Op.inputs ops).length,
    c.num_witness_variables + (Op.witnesses ops).length⟩

/-- Performing no ops leaves the counters unchanged. -/
@[simp, cs_run] theorem Counters.advance_nil (c : Counters) : c.advance ([] : List (Op F)) = c := by
  simp [Counters.advance, Op.inputs, Op.witnesses]

/-- Advancing over `l₁ ++ l₂` is advancing over `l₁`, then over `l₂`. -/
theorem Counters.advance_append (c : Counters) (l₁ l₂ : List (Op F)) :
    c.advance (l₁ ++ l₂) = (c.advance l₁).advance l₂ := by
  simp [Counters.advance, Op.inputs, Op.witnesses, Nat.add_assoc]

/-- Advancing adds the number of inputs in `ops` to the instance counter. -/
@[simp, cs_run] theorem Counters.advance_num_instance_variables (c : Counters) (ops : List (Op F)) :
    (c.advance ops).num_instance_variables = c.num_instance_variables + (Op.inputs ops).length :=
    rfl

/-- Advancing adds the number of witnesses in `ops` to the witness counter. -/
@[simp, cs_run] theorem Counters.advance_num_witness_variables (c : Counters) (ops : List (Op F)) :
    (c.advance ops).num_witness_variables = c.num_witness_variables + (Op.witnesses ops).length :=
    rfl

/-! ### Gadgets as computations on the constraint system -/

/-- A gadget: a computation against a `ConstraintSystemRef`. Given the current counters, it
returns its output and the ops it performs. `bind` advances the counters between steps. -/
structure CS (F : Type) (α : Type) where
  run : Counters → α × List (Op F)

namespace CS

variable {α β : Type}

protected def pure (x : α) : CS F α := ⟨fun _ => (x, [])⟩

protected def bind (c : CS F α) (f : α → CS F β) : CS F β :=
  ⟨fun k =>
    let r := c.run k
    let s := (f r.1).run (k.advance r.2)
    (s.1, r.2 ++ s.2)⟩

instance : Monad (CS F) where
  pure := CS.pure
  bind := CS.bind

/-- Two gadgets are equal if they behave the same from every counters. -/
@[ext] theorem ext {c d : CS F α} (h : ∀ k, c.run k = d.run k) : c = d := by
  cases c; cases d; congr; funext k; exact h k

/-- `pure x` returns `x` and performs no ops. -/
@[simp, cs_run] theorem run_pure (x : α) (k : Counters) : (pure x : CS F α).run k = (x, []) := rfl

/-- `c >>= f` runs `c`, then runs `f` on its output from the advanced counters, and performs the
ops of both. -/
@[simp, cs_run] theorem run_bind (c : CS F α) (f : α → CS F β) (k : Counters) :
    (c >>= f).run k =
      (((f (c.run k).1).run (k.advance (c.run k).2)).1,
        (c.run k).2 ++ ((f (c.run k).1).run (k.advance (c.run k).2)).2) := rfl

/-- `f <$> c` applies `f` to the output of `c` and performs the same ops. -/
@[simp, cs_run] theorem run_map (f : α → β) (c : CS F α) (k : Counters) :
    (f <$> c).run k = (f (c.run k).1, (c.run k).2) :=
  Prod.ext rfl (List.append_nil (c.run k).2)

/-- `do`-notation, `mapM`, `forM`, … behave as expected (needed by the
`List.mapM` / `List.forM` lemmas when a gadget loops over a list). -/
instance : LawfulMonad (CS F) := LawfulMonad.mk'
  (id_map := fun x => CS.ext fun k => by simp [run_map])
  (pure_bind := fun x f => CS.ext fun k => by simp [run_bind, run_pure])
  (bind_assoc := fun x f g => CS.ext fun k => by simp [run_bind, Counters.advance_append])

end CS

/-- Models `ConstraintSystemRef::new_input_variable`: allocates the next instance variable, with
value `v`. -/
def new_input_variable (v : F) : CS F Variable :=
  ⟨fun k => (.Instance k.num_instance_variables, [.input v])⟩

/-- Models `ConstraintSystemRef::new_witness_variable`: allocates the next witness variable, with
value `v`. -/
def new_witness_variable (v : F) : CS F Variable :=
  ⟨fun k => (.Witness k.num_witness_variables, [.witness v])⟩

/-- Models `ConstraintSystemRef::new_lc`. Symbolic linear combinations are inlined, so this
returns `lc` and allocates nothing. -/
def new_lc (lc : LinearCombination F) : CS F (LinearCombination F) := pure lc

/-- Models `ConstraintSystemRef::enforce_r1cs_constraint`: adds the row `a * b = c`. -/
def enforce_r1cs_constraint (a b c : LinearCombination F) : CS F Unit :=
  ⟨fun _ => ((), [.constrain ⟨a, b, c⟩])⟩

/-- `new_input_variable v` returns the next instance variable and records one input. -/
@[simp, cs_run] theorem run_new_input_variable (v : F) (k : Counters) :
    (new_input_variable v).run k = (.Instance k.num_instance_variables, [.input v]) := rfl

/-- `new_witness_variable v` returns the next witness variable and records one witness. -/
@[simp, cs_run] theorem run_new_witness_variable (v : F) (k : Counters) :
    (new_witness_variable v).run k = (.Witness k.num_witness_variables, [.witness v]) := rfl

/-- `new_lc lc` returns `lc` and performs no ops. -/
@[simp, cs_run] theorem run_new_lc (lc : LinearCombination F) (k : Counters) :
    (new_lc lc).run k = (lc, []) := rfl

/-- `enforce_r1cs_constraint a b c` records the single row `a * b = c`. -/
@[simp, cs_run] theorem run_enforce_r1cs_constraint (a b c : LinearCombination F) (k : Counters) :
    (enforce_r1cs_constraint a b c).run k = ((), [.constrain ⟨a, b, c⟩]) := rfl

/-! ### Satisfaction by an arbitrary assignment -/

/-- Every row enforced by `ops` is satisfied by the assignment `a`. No arkworks counterpart: this
is satisfaction by an arbitrary, possibly malicious, assignment. -/
def ConstraintsHold [Field F] (a : Assignment F) (ops : List (Op F)) : Prop :=
  ∀ k ∈ Op.constraints ops, k.holds a

section
variable [Field F]

/-- No ops impose no constraints. -/
@[simp, cs_run] theorem constraintsHold_nil (a : Assignment F) : ConstraintsHold a ([] : List (Op F)) := by
  simp [ConstraintsHold, Op.constraints]

/-- Allocating an input adds no constraint. -/
@[simp, cs_run] theorem constraintsHold_input (a : Assignment F) (v : F) (rest : List (Op F)) :
    ConstraintsHold a (.input v :: rest) ↔ ConstraintsHold a rest := by
  simp [ConstraintsHold, Op.constraints, Op.constraint?]

/-- Allocating a witness adds no constraint. -/
@[simp, cs_run] theorem constraintsHold_witness (a : Assignment F) (v : F) (rest : List (Op F)) :
    ConstraintsHold a (.witness v :: rest) ↔ ConstraintsHold a rest := by
  simp [ConstraintsHold, Op.constraints, Op.constraint?]

/-- Enforcing a row requires that row to hold, plus the rest. -/
@[simp, cs_run] theorem constraintsHold_constrain (a : Assignment F) (k : Constraint F)
    (rest : List (Op F)) :
    ConstraintsHold a (.constrain k :: rest) ↔ k.holds a ∧ ConstraintsHold a rest := by
  simp [ConstraintsHold, Op.constraints, Op.constraint?]

/-- The rows of `l₁ ++ l₂` hold exactly when those of `l₁` and of `l₂` both hold. -/
@[simp, cs_run] theorem constraintsHold_append (a : Assignment F) (l₁ l₂ : List (Op F)) :
    ConstraintsHold a (l₁ ++ l₂) ↔ ConstraintsHold a l₁ ∧ ConstraintsHold a l₂ := by
  simp [ConstraintsHold, Op.constraints, or_imp, forall_and]

/-- Soundness of gadget `c` against spec `P`: from any counters, every assignment that satisfies
the rows `c` enforces satisfies `P` of the output. No arkworks counterpart. -/
abbrev Sound {α : Type} (c : CS F α) (P : Assignment F → α → Prop) : Prop :=
  ∀ (k : Counters) (a : Assignment F), ConstraintsHold a (c.run k).2 → P a (c.run k).1

end

attribute [cs_run] List.append_nil List.nil_append List.singleton_append List.cons_append and_true
  true_and Constraint.holds Op.inputs Op.witnesses List.filterMap_nil List.filterMap_cons
  List.filterMap_append List.length_nil List.length_cons List.length_append Nat.add_zero
  Nat.zero_add

/-! ### The honest assignment (executable checks only) -/

/-- The assignment the prover builds while synthesising from `ConstraintSystem::new()`: each
allocated variable gets the value its closure returned, and instance 0 is the constant one. -/
def honestAssignment [Field F] (ops : List (Op F)) : Assignment F :=
  ⟨fun i => (1 :: Op.inputs ops).getD i 0, fun j => (Op.witnesses ops).getD j 0⟩

/-- Models `ConstraintSystemRef::is_satisfied`: every row holds under the prover's own
assignment. -/
def isSatisfied [Field F] [DecidableEq F] (ops : List (Op F)) : Bool :=
  let a := honestAssignment ops
  (Op.constraints ops).all fun k => decide (k.a.eval a * k.b.eval a = k.c.eval a)

end ArkR1CS
