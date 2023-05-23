import Alg.Nat.Sub
import Alg.Nat.Mul

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

theorem nat.div_def : ∀a b: nat, b ≠ .zero -> a = (a / b) * b + (a % b) := by
  apply divrem.induction
  {
    intro a b b_nz a_lt_b
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc
    match b with
    | .inc b =>
    simp
    unfold divrem.induction.bounded
    simp
    split
    simp
    rw [nat.mul_zero_left, nat.add_zero_left]
    contradiction
  }
  {
    intro a b b_nz b_le_a prev
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide at prev
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc at prev
    match b with
    | .inc b =>
    simp
    unfold divrem.induction.bounded
    simp
    split
    have := (Compare.not_lt_and_le _ _ · b_le_a)
    contradiction
    simp
    simp at prev
    rw [nat.mul_inc_left, nat.add_perm_ab_c_to_a_bc]
    rw [divrem.induction.bounded.counter_irr]
    rw [←prev]
    rw [nat.add_sub_inv]
    assumption
  }

#print axioms nat.div_def

theorem nat.from_div_def : ∀a b: nat, b ≠ .zero -> ∀ q r, r < b -> a = b * q + r -> q = a / b ∧ r = a % b := by
  apply divrem.induction
  {
    intro a b _ a_lt_b
    intro q r _ divdef
    have := nat.gt_zero a_lt_b
    match b with
    | .inc b => 
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc
    simp
    unfold divrem.induction.bounded
    split
    simp
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
    contradiction
  }
  {
    intro a b b_nz b_le_a prev
    intro q r r_lt_b divdef
    match b with
    | .inc b => 
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc
    simp
    unfold divrem.induction.bounded
    split
    have := (Compare.not_lt_and_le _ _ · b_le_a)
    contradiction
    simp
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
    
    unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide divrem.calc at qdef
    unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc at rdef
    simp at qdef rdef
    rw [divrem.induction.bounded.counter_irr]
    apply And.intro
    rw [qdef]
    rw [rdef]
  }

#print axioms nat.from_div_def
