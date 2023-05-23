import Alg.Nat.Sub
import Alg.Nat.Mul.Cmp
import Alg.Nat.Mul.Sub

structure divrem where
  quot: nat
  rem: nat

instance : Inhabited divrem where 
  default := divrem.mk .zero .zero

theorem divrem.induct.step (a b x: nat) (a_lt_x: a < x.inc) (b_le_a: ¬ a < b) (b_nz: b ≠ .zero) : a - b < x := by
  apply Compare.lt_le_trans _ (nat.lt_inc_to_le a_lt_x)
  apply nat.sub_is_lt
  apply nat.ne_zero_to_gt_zero b_nz
  exact Compare.not_lt_is_le b_le_a

def divrem.induction.bounded {P : ∀_ b, b ≠ .zero -> Sort _ }
  (x: nat)
  (base: ∀(a b: nat) (h: b ≠ .zero), a < b -> P a b h)
  (induct: ∀(a b: nat) (h: b ≠ .zero), b <= a -> P (a - b) b h -> P a b h):
  ∀(a b: nat) (h: b ≠ .zero), a < x -> P a b h := 
  fun a b b_nz a_lt_x =>
  match x with
  | .zero => ((nat.not_lt_zero _) a_lt_x).elim
  | .inc x => 
  match Compare.dec_lt a b with
  | .isTrue h => base a b b_nz h
  | .isFalse h => 
    let h := Compare.not_lt_is_le h
    induct a b b_nz h (divrem.induction.bounded x base induct (a - b) b b_nz (by
      next b_le_a => {
        exact divrem.induct.step a b x a_lt_x b_le_a b_nz
      }))

#print axioms divrem.induction.bounded

def divrem.induction.bounded.counter_irr {P : ∀_ b, b ≠ .zero -> Sort _ }
  (x y: nat)
  (base: ∀(a b: nat) (h: b ≠ .zero), a < b -> P a b h)
  (induct: ∀(a b: nat) (h: b ≠ .zero), b <= a -> P (a - b) b h -> P a b h):
  ∀(a b: nat) (h: b ≠ .zero), (a_lt_x: a < x) -> (a_lt_y: a < y) ->
  divrem.induction.bounded x base induct a b h a_lt_x =
  divrem.induction.bounded y base induct a b h a_lt_y
   := by
  intro a b b_nz a_lt_x a_lt_y
  unfold bounded
  match x, y with
  | .zero, _ => exact ((nat.not_lt_zero _) a_lt_x).elim
  | _, .zero => exact ((nat.not_lt_zero _) a_lt_y).elim
  | .inc x, .inc y =>
  match Compare.dec_lt a b with
  | .isTrue h => rfl
  | .isFalse h => 
    simp
    have := divrem.induction.bounded.counter_irr x y base induct (a - b) b b_nz (
      divrem.induct.step a b x a_lt_x h b_nz) (
        divrem.induct.step a b y a_lt_y h b_nz)
    rw [this]

#print axioms divrem.induction.bounded.counter_irr

def divrem.induction {P : ∀_ b, b ≠ .zero -> Sort _ }
  (base: ∀(a b: nat) (h: b ≠ .zero), a < b -> P a b h)
  (induct: ∀(a b: nat) (h: b ≠ .zero), b <= a -> P (a - b) b h -> P a b h):
  ∀(a b: nat) (h: b ≠ .zero), P a b h := 
    fun a b h => divrem.induction.bounded a.inc base induct a b h (nat.lt_inc _)

#print axioms divrem.induction

def divrem.calc (a b: nat) (h: b ≠ .zero): divrem := 
    divrem.induction.bounded a.inc
      (fun a _ _ _ => divrem.mk nat.zero a)
      (fun _ _ _ _ prev => divrem.mk prev.quot.inc prev.rem)
      a b h (nat.lt_inc _)

#print axioms divrem.calc

def divrem.calc.of_bounded (a b: nat) (h: b ≠ .zero) :
  ∀ x xh,
  divrem.induction.bounded x
      (fun a _ _ _ => divrem.mk nat.zero a)
      (fun _ _ _ _ prev => divrem.mk prev.quot.inc prev.rem)
      a b h xh = divrem.calc a b h := by
  intro x xh
  unfold divrem.calc
  rw [divrem.induction.bounded.counter_irr]

def nat.divide (a b: nat) (b_nz: b ≠ .zero) := (divrem.calc a b b_nz).quot
def nat.remainder (a b: nat) (b_nz: b ≠ .zero) := (divrem.calc a b b_nz).rem

instance nat.Div : Div nat where
  div x y := match y with
    | .zero => .zero
    | .inc y₀ => nat.divide x y₀.inc nat.noConfusion

instance nat.Rem : Mod nat where
  mod x y := match y with
    | .zero => .zero
    | .inc y₀ => nat.remainder x y₀.inc nat.noConfusion

def nat.divide.of_calc (a b: nat) (h: b ≠ .zero) :
  (divrem.calc a b h).quot = a / b := by
  match b with
  | .inc _ =>
  rfl

def nat.remainder.of_calc (a b: nat) (h: b ≠ .zero) :
  (divrem.calc a b h).rem = a % b := by
  match b with
  | .inc _ =>
  rfl

theorem nat.divide.base { a b : nat } (a_lt_b: a < b) (b_nz: b ≠ .zero) : a / b = .zero := by
  conv => {
    lhs
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide
  }
  match b with
  | .inc b =>
  simp
  unfold divrem.calc divrem.induction.bounded
  split
  rfl
  have := (Compare.not_lt_and_le _ _ a_lt_b)
  contradiction

#print axioms nat.divide.base

theorem nat.remainder.base { a b : nat } (a_lt_b: a < b) (b_nz: b ≠ .zero) : a % b = a := by
  conv => {
    lhs
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder
  }
  match b with
  | .inc b =>
  simp
  unfold divrem.calc divrem.induction.bounded
  split
  rfl
  have := (Compare.not_lt_and_le _ _ a_lt_b)
  contradiction

#print axioms nat.remainder.base

theorem nat.divide.induct { a b : nat } (b_le_a: b <= a) (b_nz: b ≠ .zero) : a / b = ((a - b) / b).inc := by
  conv => {
    lhs
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide
  }
  match b with
  | .inc b =>
  simp
  unfold divrem.calc divrem.induction.bounded
  split
  have := (Compare.not_lt_and_le _ _ · b_le_a)
  contradiction
  rw [divrem.calc.of_bounded, nat.divide.of_calc]

#print axioms nat.divide.induct

theorem nat.remainder.induct { a b : nat } (b_le_a: b <= a) (b_nz: b ≠ .zero) : a % b = (a - b) % b := by
  conv => {
    lhs
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder
  }
  match b with
  | .inc b =>
  simp
  unfold divrem.calc divrem.induction.bounded
  split
  have := (Compare.not_lt_and_le _ _ · b_le_a)
  contradiction
  simp
  rw [divrem.calc.of_bounded, nat.remainder.of_calc]

#print axioms nat.remainder.induct

theorem nat.div_def : ∀a b: nat, b ≠ .zero -> a = (a / b) * b + (a % b) := by
  apply divrem.induction
  {
    intro a b b_nz a_lt_b
    rw [nat.divide.base, nat.remainder.base]
    rw [nat.mul_zero_left, nat.add_zero_left]
    repeat assumption
  }
  {
    intro a b b_nz b_le_a prev
    rw [nat.divide.induct, nat.remainder.induct]
    rw [nat.mul_inc_left, nat.add_perm_ab_c_to_a_bc]
    rw [←prev]
    rw [nat.add_sub_inv]
    repeat assumption
  }

#print axioms nat.div_def

theorem nat.from_div_def : ∀a b: nat, b ≠ .zero -> ∀ q r, r < b -> a = b * q + r -> q = a / b ∧ r = a % b := by
  apply divrem.induction
  {
    intro a b _ a_lt_b
    intro q r _ divdef
    rw [nat.divide.base, nat.remainder.base]
    cases q
    apply And.intro
    rfl
    rw [nat.mul_zero_right, nat.add_zero_left] at divdef
    exact divdef.symm
    rw [nat.mul_inc_right, nat.add_perm_ab_c_to_a_bc] at divdef
    rw [divdef] at a_lt_b
    have := Compare.le_lt_trans (nat.a_le_a_add_b _ _) a_lt_b
    have := Compare.not_lt_id this
    contradiction
    repeat assumption
  }
  {
    intro a b b_nz b_le_a prev
    intro q r r_lt_b divdef
    match q with
    | .zero =>
      rw [nat.mul_zero_right, nat.add_zero_left] at divdef
      rw [←divdef] at r_lt_b
      have := Compare.not_lt_and_le _ _ r_lt_b b_le_a
      contradiction
    | .inc q₀ =>
      have ⟨ qdef, rdef ⟩  := prev q₀ r r_lt_b (by
        rw [divdef]
        rw [nat.mul_inc_right]
        rw [nat.add_perm_ab_c_to_a_bc, nat.sub_add_inv])
      apply And.intro
      rw [nat.divide.induct, qdef]
      repeat assumption
      rw [nat.remainder.induct, rdef]
      repeat assumption
    repeat assumption  
  }

#print axioms nat.from_div_def

theorem nat.rem_lt : ∀(a b: nat), b ≠ zero -> a % b < b  := by
  apply divrem.induction

  {
    intro a b b_nz a_lt_b
    rw [nat.remainder.base]
    repeat assumption
  }

  {
    intro a b b_nz b_le_a prev
    rw [nat.remainder.induct b_le_a]
    repeat assumption
  }

#print axioms nat.rem_lt

theorem nat.rem_le: ∀(a b: nat), b ≠ zero -> a % b <= a  := by
  apply divrem.induction

  {
    intro a b b_nz a_lt_b
    rw [nat.remainder.base]
    apply Compare.le_id
    repeat assumption
  }

  {
    intro a b b_nz a_ge_b prev
    rw [nat.remainder.induct]
    apply Compare.le_trans prev
    apply nat.sub_is_le
    repeat assumption
  }

#print axioms nat.rem_lt

axiom Test : False

theorem nat.of_mul_rem: ∀(a b: nat), b ≠ zero -> f * (a % b) = (f * a) % (f * b)  := by
  apply divrem.induction

  {
    intro a b b_nz a_lt_b
    match f with
    | .zero =>
      rw [nat.mul_zero_left, nat.mul_zero_left, nat.mul_zero_left]
      rfl
    | .inc f =>
    rw [nat.remainder.base, nat.remainder.base]
    apply nat.to_lt_mul_left_irr
    any_goals assumption
    exact nat.noConfusion
    match b with
    | .inc b =>
    rw [nat.mul_inc_left, nat.add_inc_left]
    exact nat.noConfusion
  }

  {
    intro a b b_nz a_ge_b prev
    match f with
    | .zero =>
      rw [nat.mul_zero_left, nat.mul_zero_left, nat.mul_zero_left]
      rfl
    | .inc f =>
      rw [nat.remainder.induct]
      conv => {
        rhs
        rw [nat.remainder.induct (by
          apply nat.to_le_mul_left_irr
          assumption) (by
          match b with
          | .inc b =>
          rw [nat.mul_inc_left, nat.add_inc_left]
          exact nat.noConfusion)]
        rw [←nat.mul_sub_left _ _ _  (by assumption)]
      }
      repeat assumption
  }

#print axioms nat.of_mul_rem
