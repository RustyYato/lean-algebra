import Alg.Nat.Sub
import Alg.Nat.Mul

structure divrem where
  quot: nat
  rem: nat

instance : Inhabited divrem where 
  default := divrem.mk .zero .zero

def divrem.calc_bounded (x a b: nat) : b ≠ nat.zero -> Option divrem := fun b_nz => match x with
  | .zero => .none
  | .inc x₀ => match Compare.dec_lt a b with
    | .isTrue _ => .some (divrem.mk .zero a)
    | .isFalse _ => match divrem.calc_bounded x₀ (a - b) b b_nz with
      | .none => .none
      | .some dr => .some (divrem.mk (dr.quot.inc) dr.rem)

#print axioms divrem.calc_bounded

def divrem.calc_bounded.is_some (x a b: nat) : (b_nz: b ≠ .zero) -> a < x -> (divrem.calc_bounded x a b b_nz).isSome := by
  intro b_nz a_lt_x
  have := nat.gt_zero a_lt_x
  match b with
  | .inc b₀ =>
  match x with
  | .inc .zero =>
    match a with
    | .inc a₀ =>
      have := nat.of_lt_inc_irr a_lt_x
      have := nat.gt_zero this
      contradiction
    | .zero =>
      have : nat.zero < b₀.inc := nat.zero_lt_inc b₀
      unfold calc_bounded
      split
      rfl
      contradiction
  | .inc (.inc x₀) =>
    unfold calc_bounded
    split
    rfl
    split
    next b_le_a _ _ h => {
      have := divrem.calc_bounded.is_some x₀.inc (a - nat.inc b₀) b₀.inc b_nz (by
        apply Compare.lt_le_trans _ (nat.lt_inc_to_le a_lt_x)
        apply nat.sub_is_lt
        apply nat.zero_lt_inc
        exact Compare.not_lt_is_le b_le_a)
      rw [h] at this
      contradiction
    }
    rfl

#print axioms divrem.calc_bounded.is_some

def divrem.calc_bounded.counter_irr (x y a b: nat) : (b_nz: b ≠ .zero) ->
  a < x ->
  a < y ->
  divrem.calc_bounded x a b b_nz = divrem.calc_bounded y a b b_nz := by
  intro b_nz a_lt_x a_lt_y
  have := nat.gt_zero a_lt_x
  have := nat.gt_zero a_lt_y
  have x_is_some := divrem.calc_bounded.is_some x a b b_nz a_lt_x
  have y_is_some := divrem.calc_bounded.is_some y a b b_nz a_lt_y
  match b with
  | .inc b₀ =>
  match x, y with
  | .inc .zero, .inc .zero => rfl
  | .inc .zero, .inc (.inc y) =>
    unfold calc_bounded
    split
    rfl
    unfold calc_bounded at x_is_some
    next h => {
      rw [h] at x_is_some
      simp at x_is_some
      unfold calc_bounded at x_is_some
      conv at x_is_some => {
        congr
        simp
      }
      contradiction
    }
  | .inc (.inc x), .inc .zero =>
    unfold calc_bounded
    split
    rfl
    unfold calc_bounded at y_is_some
    next h => {
      rw [h] at y_is_some
      simp at y_is_some
      unfold calc_bounded at y_is_some
      conv at y_is_some => {
        congr
        simp
      }
      contradiction
    }
  | .inc (.inc x), .inc (.inc y) => {
    unfold calc_bounded
    split
    rfl
    simp
    have : calc_bounded (nat.inc x) (a - nat.inc b₀) (nat.inc b₀) b_nz = calc_bounded (nat.inc y) (a - nat.inc b₀) (nat.inc b₀) b_nz := by
      apply divrem.calc_bounded.counter_irr
      next b_le_a _ => {
        apply Compare.lt_le_trans _ (nat.lt_inc_to_le a_lt_x)
        apply nat.sub_is_lt
        apply nat.zero_lt_inc
        exact Compare.not_lt_is_le b_le_a
      }
      next b_le_a _ => {
        apply Compare.lt_le_trans _ (nat.lt_inc_to_le a_lt_y)
        apply nat.sub_is_lt
        apply nat.zero_lt_inc
        exact Compare.not_lt_is_le b_le_a
      }
    rw [this]
  }

#print axioms divrem.calc_bounded.counter_irr

def divrem.calc (a b: nat) (b_nz: b ≠ .zero) : divrem := match h:divrem.calc_bounded a.inc a b b_nz with
  | .some x => x
  | .none => by
    have := divrem.calc_bounded.is_some a.inc a b b_nz (nat.lt_inc _)
    rw [h] at this
    contradiction

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

theorem divrem.calc_eq_bounded_helper (a b: nat) (b_nz: b ≠ .zero) : .some (divrem.calc a b b_nz) = divrem.calc_bounded a.inc a b b_nz := by
  unfold divrem.calc
  split
  next h => { rw [h] }
  next h => {
    have := divrem.calc_bounded.is_some a.inc a b b_nz (nat.lt_inc _)
    rw [h] at this
    contradiction
  }

#print axioms divrem.calc_eq_bounded_helper

theorem divrem.bounded_eq_calc (a b: nat) (b_nz: b ≠ .zero) : ∀x, a < x -> divrem.calc_bounded x a b b_nz = .some (divrem.calc a b b_nz) := by
  intro x a_lt_x
  rw [divrem.calc_eq_bounded_helper]
  apply divrem.calc_bounded.counter_irr
  assumption
  apply nat.lt_inc

#print axioms divrem.bounded_eq_calc

def divrem.induction {P : ∀_ b, b ≠ .zero -> Prop }
  (base: ∀(a b: nat) (h: b ≠ .zero), a < b -> P a b h)
  (induct: ∀(a b: nat) (h: b ≠ .zero), b <= a -> P (a - b) b h -> P a b h):
  ∀(a b: nat) (h: b ≠ .zero), P a b h := 
  fun a b b_nz =>
  match Compare.dec_lt a b with
  | .isTrue h => base a b b_nz h
  | .isFalse h => 
    let h := Compare.not_lt_is_le h
    induct a b b_nz h (divrem.induction base induct (a - b) b b_nz)
termination_by _ => a
decreasing_by {
  simp_wf
  apply nat.sub_is_lt
  exact nat.ne_zero_to_gt_zero b_nz
  exact h
}

#print axioms divrem.induction

theorem nat.div_base { a b: nat } : a < b -> a / b = nat.zero := by
  intro a_lt_b
  have := nat.gt_zero a_lt_b
  match b with
  | .inc b₀ =>
  unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide divrem.calc
  simp
  have is_some := divrem.calc_bounded.is_some a.inc a b₀.inc nat.noConfusion (nat.lt_inc _)
  split
  {
    next h => {
      unfold divrem.calc_bounded at h
      split at h
      rw [←Option.some.inj h]
      contradiction
    }
  }
  next h => {
    rw [h] at is_some
    contradiction
  }

#print axioms nat.div_base

theorem nat.div_induct { a b: nat } : b ≠ .zero -> b <= a -> a / b = ((a - b) / b).inc := by
  intro b_ne_zero b_le_a
  match b with
  | .inc b₀ =>
  unfold HDiv.hDiv instHDiv Div.div nat.Div nat.divide divrem.calc
  simp
  have is_some := divrem.calc_bounded.is_some a.inc a b₀.inc nat.noConfusion (nat.lt_inc _)
  split
  {
    next h => {
      unfold divrem.calc_bounded at h
      split at h
      rw [←Option.some.inj h]
      next a_lt_b _ => {
        have := Compare.not_lt_and_le _ _ a_lt_b b_le_a
        contradiction
      }
      rw [divrem.bounded_eq_calc] at h
      rw [←Option.some.inj h]
      split
      next h₀ => {
        rw [Option.some.inj h]
        rw [divrem.bounded_eq_calc] at h₀
        rw [h₀] at h
        have h := Option.some.inj h
        rw [←h]
        apply nat.lt_inc
      }
      have := divrem.calc_bounded.is_some (a - b₀.inc).inc (a - b₀.inc) b₀.inc nat.noConfusion (nat.lt_inc _)
      next h => {
        rw [h] at this
        contradiction
      }
      apply nat.sub_is_lt
      apply nat.zero_lt_inc
      assumption
    }
  }
  next h => {
    rw [h] at is_some
    contradiction
  }

#print axioms nat.div_induct

theorem nat.rem_base { a b: nat } : a < b -> a % b = a := by
  intro a_lt_b
  have := nat.gt_zero a_lt_b
  match b with
  | .inc b₀ =>
  unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc
  simp
  have is_some := divrem.calc_bounded.is_some a.inc a b₀.inc nat.noConfusion (nat.lt_inc _)
  split
  {
    next h => {
      unfold divrem.calc_bounded at h
      split at h
      rw [←Option.some.inj h]
      contradiction
    }
  }
  next h => {
    rw [h] at is_some
    contradiction
  }

#print axioms nat.rem_base

theorem nat.rem_induct { a b: nat } : b ≠ .zero -> b <= a -> a % b = ((a - b) % b) := by
  intro b_ne_zero b_le_a
  match b with
  | .inc b₀ =>
  unfold HMod.hMod instHMod Mod.mod nat.Rem nat.remainder divrem.calc
  simp
  have is_some := divrem.calc_bounded.is_some a.inc a b₀.inc nat.noConfusion (nat.lt_inc _)
  split
  {
    next h => {
      unfold divrem.calc_bounded at h
      split at h
      rw [←Option.some.inj h]
      next a_lt_b _ => {
        have := Compare.not_lt_and_le _ _ a_lt_b b_le_a
        contradiction
      }
      rw [divrem.bounded_eq_calc] at h
      rw [←Option.some.inj h]
      split
      next h₀ => {
        rw [Option.some.inj h]
        rw [divrem.bounded_eq_calc] at h₀
        rw [h₀] at h
        have h := Option.some.inj h
        rw [←h]
        apply nat.lt_inc
      }
      have := divrem.calc_bounded.is_some (a - b₀.inc).inc (a - b₀.inc) b₀.inc nat.noConfusion (nat.lt_inc _)
      next h => {
        rw [h] at this
        contradiction
      }
      apply nat.sub_is_lt
      apply nat.zero_lt_inc
      assumption
    }
  }
  next h => {
    rw [h] at is_some
    contradiction
  }

#print axioms nat.rem_induct

theorem nat.div_def : ∀a b: nat, b ≠ .zero -> a = (a / b) * b + (a % b) := by
  apply divrem.induction
  {
    intro a b b_nz a_lt_b
    rw [nat.div_base a_lt_b, nat.mul_zero_left, nat.add_zero_left, nat.rem_base a_lt_b]
  }
  {
    intro a b b_nz b_le_a prev
    rw [nat.div_induct b_nz b_le_a]
    rw [nat.mul_inc_left, nat.add_perm_ab_c_to_a_bc]
    rw [nat.rem_induct b_nz b_le_a]
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
    rw [nat.div_base a_lt_b, nat.rem_base a_lt_b]
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
  }
  {
    intro a b b_nz b_le_a prev
    intro q r r_lt_b divdef
    rw [nat.div_induct b_nz b_le_a, nat.rem_induct b_nz b_le_a]
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
    exact nat.to_inc_irr qdef
    exact rdef
  }

#print axioms nat.from_div_def
