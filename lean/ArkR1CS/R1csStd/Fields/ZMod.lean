/-
# `FpVar` over `ZMod p`

Facts that need a prime field, where a field element is read as a number
through `ZMod.val`: comparing with a small constant, and reading the bits of
`to_bits_le_with_top_bits_zero` as the digits of a number.
-/
import ArkR1CS.R1csStd.Fields.Fp
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Digits.Defs

namespace ArkR1CS

variable {p : Nat} [Fact p.Prime]

/-- A field element equals the small constant `i` exactly when its value is `i`. -/
theorem ZMod.eq_natCast_iff (x : ZMod p) {i : Nat} (hi : i < p) :
    x = (i : ZMod p) ↔ x.val = i := by
  constructor
  · rintro rfl
    exact ZMod.val_cast_of_lt hi
  · intro h
    rw [← h, ZMod.natCast_zmod_val]

/-- A bit has value 0 or 1. -/
theorem ZMod.val_lt_two_of_bit {x : ZMod p} (hx : x = 0 ∨ x = 1) : x.val < 2 := by
  rcases hx with rfl | rfl
  · simp
  · rw [ZMod.val_one]; norm_num

namespace FpVar

/-- `value.is_eq(Constant(i))` for a small `i` is the bit of `value = i`, read as numbers. -/
theorem is_eq_const_bit (value : FpVar (ZMod p)) {i : Nat} (hi : i < p) {k : Counters}
    {a : Assignment (ZMod p)}
    (h : ConstraintsHold a
      ((EqGadget.is_eq (F := ZMod p) value (FpVar.Constant (i : ZMod p))).run k).2) :
    IsBit a ((EqGadget.is_eq (F := ZMod p) value (FpVar.Constant (i : ZMod p))).run k).1
      ((value.eval a).val = i) :=
  (is_eq_bit _ _ h).congr (by simp [ZMod.eq_natCast_iff _ hi])

end FpVar

/-! ### Bits as digits -/

/-- A run of little-endian binary digits is the matching bits of their value. -/
theorem ofDigits_drop_take (L : List Nat) (hL : ∀ x ∈ L, x < 2) (m r : Nat)
    (hmr : m + r ≤ L.length) :
    Nat.ofDigits 2 ((L.drop m).take r) = Nat.ofDigits 2 L / 2 ^ m % 2 ^ r := by
  have hlt : ∀ l : List Nat, (∀ x ∈ l, x < 2) → Nat.ofDigits 2 l < 2 ^ l.length :=
    fun l hl => Nat.ofDigits_lt_base_pow_length (by norm_num) hl
  have h1 : Nat.ofDigits 2 (L.take m) < 2 ^ m := by
    have := hlt (L.take m) fun x hx => hL x (List.mem_of_mem_take hx)
    rwa [List.length_take_of_le (by omega)] at this
  have h2 : Nat.ofDigits 2 ((L.drop m).take r) < 2 ^ r := by
    have := hlt ((L.drop m).take r) fun x hx =>
      hL x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
    rwa [List.length_take_of_le (by simp; omega)] at this
  conv_rhs => rw [← List.take_append_drop m L, Nat.ofDigits_append]
  rw [List.length_take_of_le (by omega), Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt h1, Nat.zero_add]
  conv_rhs => rw [← List.take_append_drop r (L.drop m), Nat.ofDigits_append]
  rw [List.length_take_of_le (by simp; omega), Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

/-- `leBitsValue` of natural-number digits is the number they spell. -/
theorem leBitsValue_natCast {F : Type} [Field F] (L : List Nat) :
    leBitsValue (L.map (Nat.cast : Nat → F)) = ((Nat.ofDigits 2 L : Nat) : F) := by
  rw [Nat.coe_ofDigits]
  induction L with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, leBitsValue_cons, ih, Nat.ofDigits, Nat.cast_ofNat]

namespace FpVar

/-- Soundness of `to_bits_le_with_top_bits_zero(size)` read as numbers: `self` is below
`2^size`, and `le_bits_to_fp` of bits `m .. m + r` is `self / 2^m % 2^r`. -/
theorem to_bits_le_with_top_bits_zero_val (x : FpVar (ZMod p)) (hx : ¬ x.isConstant)
    (size : Nat) (hp : 2 ^ size < p) (k : Counters) (a : Assignment (ZMod p))
    (h : ConstraintsHold a ((x.to_bits_le_with_top_bits_zero size).run k).2) :
    let bits := ((x.to_bits_le_with_top_bits_zero size).run k).1.1
    (x.eval a).val < 2 ^ size ∧
      ∀ m r, m + r ≤ size → (Boolean.le_bits_to_fp ((bits.drop m).take r)).eval a =
        (((x.eval a).val / 2 ^ m % 2 ^ r : Nat) : ZMod p) := by
  obtain ⟨hlen, hbit, hval⟩ := to_bits_le_with_top_bits_zero_sound x hx size k a h
  intro bits
  -- Read the bits as base-2 digits `L`, so that `self` is the number they spell.
  set L := bits.map fun b => (b.eval a).val
  have hL : ∀ y ∈ L, y < 2 := by
    simp only [L, List.mem_map]
    rintro _ ⟨b, hb, rfl⟩
    exact ZMod.val_lt_two_of_bit (hbit b hb)
  have hcast : ∀ l : List (Boolean (ZMod p)), l.map (·.eval a) =
      (l.map fun b => (b.eval a).val).map (Nat.cast : Nat → ZMod p) := by
    intro l; simp [Function.comp_def]
  have hLlen : L.length = size := by simp [L, hlen, bits]
  have hNlt : Nat.ofDigits 2 L < 2 ^ size := by
    rw [← hLlen]; exact Nat.ofDigits_lt_base_pow_length (by norm_num) hL
  have hN : (x.eval a).val = Nat.ofDigits 2 L := by
    rw [hval, hcast, leBitsValue_natCast, ZMod.val_cast_of_lt (hNlt.trans hp)]
  refine ⟨hN ▸ hNlt, fun m r hmr => ?_⟩
  rw [Boolean.eval_le_bits_to_fp, hcast, List.map_take, List.map_drop, leBitsValue_natCast, hN,
    ofDigits_drop_take L hL m r (hLlen ▸ hmr)]

end FpVar

end ArkR1CS
