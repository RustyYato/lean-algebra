inductive Order := | Less | Eq | Greater

@[simp]
def Order.flip (c: Order) : Order := match c with
| Less => Greater | Eq => Eq | Greater => Less

#print axioms Order.flip

@[simp]
def Order.flip_lt : Order.Less.flip = Order.Greater := rfl

#print axioms Order.flip_lt

@[simp]
def Order.flip_gt : Order.Greater.flip = Order.Less := rfl

#print axioms Order.flip_gt

@[simp]
def Order.flip_eq : Order.Eq.flip = Order.Eq := rfl

#print axioms Order.flip_eq

def Order.swap_flip {a b: Order} : a.flip = b -> a = b.flip := fun _ => match a, b with
| .Less, .Greater 
| .Eq, .Eq 
| .Greater, .Less => rfl

#print axioms Order.swap_flip

def Order.flip_flip (o: Order) : o.flip.flip = o := by
  cases o <;> rfl

#print axioms Order.flip_flip

class Compare (α: Sort _) where
  ord (_ _: α) : Order

  ord_transitive {{ o: Order }} (_: ord a b = o) (_: ord b c = o) : (ord a c = o)
  ord_flip (a b: α) : (ord a b) = (ord b a).flip

  ord_id (a: α) : (ord a a = Order.Eq) 
  ord_to_eq (_: ord a b = Order.Eq) : a = b

  lt a b := ord a b = Order.Less

#print axioms Compare

instance ord_lt [Compare α] : LT α where
  lt a b := Compare.ord a b = Order.Less
instance ord_le [Compare α] : LE α where
  le a b := Compare.ord a b = Order.Less ∨ Compare.ord a b = Order.Eq

#print axioms ord_lt
#print axioms ord_le

theorem Compare.ord_symm {{ α: Sort _ }} [Compare α] (a b: α) : ord a b = Order.Eq -> ord b a = Order.Eq := by
  intro ab_eq
  have ab_eq := ord_to_eq ab_eq
  rw [ab_eq]
  exact ord_id _

#print axioms Compare.ord_symm

def Compare.flip {{ α: Sort _ }} [Compare α] {{ a b : α }} {o: Order} : ord a b = o -> ord b a = o.flip := by
  intro ord_ab
  rw [Compare.ord_flip] at ord_ab
  exact Order.swap_flip ord_ab

#print axioms Compare.flip

def Compare.of_flip {{ α: Sort _ }} [Compare α] {{ a b : α }} {o: Order} : ord a b = o.flip -> ord b a = o := by
  intro ord_ab
  have ord_ab := Compare.flip ord_ab
  rw [Order.flip_flip] at ord_ab
  exact ord_ab

#print axioms Compare.of_flip

def Compare.ord_flip_ne {{ α: Sort _ }} [Compare α] {{ a b : α }} {{ o: Order }} (ord_ab: ord a b ≠ o) : (ord b a ≠ o.flip) := by
  intro ord_ba
  rw [ord_flip] at ord_ba
  cases o <;> cases h:ord a b
  any_goals contradiction
  any_goals (rw [h] at ord_ba; contradiction)

#print axioms Compare.ord_flip_ne

def Compare.ord_ne_transitive {{ α: Sort _ }} [Compare α] {{ a b c : α }} {{ o : Order }} : 
    o ≠ Order.Eq -> ord a b ≠ o -> ord b c ≠ o  -> ord a c ≠ o := by
      intro o_not_eq ab_ne_o bc_ne_o
      match h:o with
      | .Eq => contradiction
      | .Less =>
        intro ac_less
        match h₀:ord a b with
        | .Less => contradiction
        | .Eq =>
            match h₁:ord b c with  
              | .Less => contradiction
              | .Eq =>
                have ac_eq := ord_transitive h₀ h₁
                rw [ac_less] at ac_eq
                contradiction
              | .Greater =>
                have a_eq_b := ord_to_eq h₀
                rw [←a_eq_b] at h₁
                rw [ac_less] at h₁
                contradiction
        | .Greater =>
          match h₁:ord b c with  
            | .Less => contradiction
            | .Eq =>
              have a_eq_b := ord_to_eq h₁
              rw [a_eq_b] at h₀
              rw [ac_less] at h₀
              contradiction
            | .Greater =>
              have ac_eq := ord_transitive h₀ h₁
              rw [ac_less] at ac_eq
              contradiction
      | .Greater =>
        intro ac_greater
        match h₀:ord a b with
        | .Less =>
          match h₁:ord b c with  
            | .Less => 
              have ac_eq := ord_transitive h₀ h₁
              rw [ac_greater] at ac_eq
              contradiction
            | .Eq =>
              have a_eq_b := ord_to_eq h₁
              rw [a_eq_b] at h₀
              rw [ac_greater] at h₀
              contradiction
            | .Greater => contradiction
        | .Eq =>
            match h₁:ord b c with  
              | .Less => 
                have a_eq_b := ord_to_eq h₀
                rw [←a_eq_b] at h₁
                rw [ac_greater] at h₁
                contradiction
              | .Eq =>
                have ac_eq := ord_transitive h₀ h₁
                rw [ac_greater] at ac_eq
                contradiction
              | .Greater => contradiction
        | .Greater => contradiction

#print axioms Compare.ord_ne_transitive

def Compare.ord_from_eq {{ α: Sort _ }} [Compare α] {{ a b : α }} : a = b -> ord a b = Order.Eq := by
  intro a_eq_b
  rw [a_eq_b]
  apply ord_id

#print axioms Compare.ord_from_eq

def Compare.le_id {{ α: Sort _ }} [Compare α] (a: α) :
  a <= a := by
  apply Or.inr
  exact Compare.ord_id _

#print axioms Compare.le_id

def Compare.lt_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a < b -> b < c -> a < c := by
  intro a_lt_b b_lt_c
  have a_lt_c := ord_transitive a_lt_b b_lt_c
  exact a_lt_c

#print axioms Compare.lt_trans

def Compare.le_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a <= b -> b <= c -> a <= c := by
  intro a_lt_b b_lt_c
  cases a_lt_b <;> cases b_lt_c
  apply Or.inl
  apply @Compare.lt_trans _ _ a b c
  assumption
  assumption
  apply Or.inl
  have b_eq_c : b = c := Compare.ord_to_eq (by assumption)
  rw [←b_eq_c]
  assumption
  apply Or.inl
  have a_eq_b : a = b := Compare.ord_to_eq (by assumption)
  rw [a_eq_b]
  assumption
  apply Or.inr
  apply @Compare.ord_transitive _ _ a b c <;> assumption

#print axioms Compare.le_trans

def Compare.lt_le_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a < b -> b <= c -> a < c := by
  intro a_lt_b b_lt_c
  cases b_lt_c
  apply @Compare.lt_trans _ _ a b c
  assumption
  assumption
  have b_eq_c : b = c := Compare.ord_to_eq (by assumption)
  rw [←b_eq_c]
  assumption

#print axioms Compare.lt_le_trans

def Compare.le_lt_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a <= b -> b < c -> a < c := by
  intro a_lt_b b_lt_c
  cases a_lt_b
  apply Compare.lt_trans
  assumption
  assumption
  have a_eq_b : a = b := Compare.ord_to_eq (by assumption)
  rw [a_eq_b]
  assumption

#print axioms Compare.le_trans

def Compare.gt_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a < b -> b < c -> a < c := by
  apply Compare.lt_trans

#print axioms Compare.gt_trans

def Compare.ge_trans {{ α: Sort _ }} [Compare α] {{ a b c: α }} :
  a <= b -> b <= c -> a <= c := by
  apply Compare.le_trans

#print axioms Compare.ge_trans

def dec_true : Decidable True := Decidable.isTrue True.intro
def dec_false : Decidable False := Decidable.isFalse False.elim

#print axioms dec_true
#print axioms dec_false

def dec_or : Decidable A -> Decidable B -> Decidable (A ∨ B) := by
  intro deca decb
  cases deca <;> cases decb
  apply Decidable.isFalse
  intro a_or_b
  cases a_or_b <;> contradiction
  all_goals apply Decidable.isTrue
  any_goals (apply Or.inr; assumption)
  apply Or.inl; assumption

#print axioms dec_or

def dec_and: Decidable A -> Decidable B -> Decidable (A ∧ B) := by
  intro deca decb
  cases deca <;> cases decb
  apply Decidable.isFalse
  intro a_or_b
  cases a_or_b <;> contradiction
  apply Decidable.isFalse
  intro a_and_b
  have := a_and_b.left
  contradiction
  apply Decidable.isFalse
  intro a_and_b
  have := a_and_b.right
  contradiction
  apply Decidable.isTrue
  apply And.intro <;> assumption

#print axioms dec_and

instance Order.dec_eq (a b: Order) : Decidable (a = b) := match a, b with
| .Less, .Less | .Eq, .Eq | .Greater, .Greater => Decidable.isTrue rfl
| .Less, .Eq | .Eq, .Less | .Greater, .Less
| .Less, .Greater | .Eq, .Greater | .Greater, .Eq => Decidable.isFalse Order.noConfusion

instance Order.dec_ne (a b: Order) : Decidable (¬a = b) :=
   match a.dec_eq b with
   | .isTrue a_eq_b => Decidable.isFalse (fun x => x a_eq_b)
   | .isFalse a_ne_b => Decidable.isTrue a_ne_b

#print axioms Order.dec_eq
#print axioms Order.dec_ne

instance Compare.dec_eq [Compare α] (a b: α) : Decidable (a = b) := by
  match h:Compare.ord a b with
  | .Greater | .Less =>
    apply Decidable.isFalse
    intro a_eq_b
    rw [a_eq_b, Compare.ord_id] at h
    contradiction
  | .Eq =>
    apply Decidable.isTrue
    apply Compare.ord_to_eq
    assumption

#print axioms Compare.dec_eq

instance Compare.dec_ne [Compare α] (a b: α) : Decidable (a ≠ b) := match Compare.dec_eq a b with
   | .isTrue a_eq_b => Decidable.isFalse (fun not_a_eq_b => not_a_eq_b a_eq_b)
   | .isFalse a_ne_b => Decidable.isTrue a_ne_b

#print axioms Compare.dec_ne

instance Compare.dec_lt [Compare α] (a b: α) : Decidable (a < b) := by
  simp
  apply Order.dec_eq

#print axioms Compare.dec_lt

instance Compare.dec_le [Compare α] (a b: α) : Decidable (a <= b) := by
  simp
  apply dec_or <;> apply Order.dec_eq

#print axioms Compare.dec_le

instance Compare.dec_gt [Compare α] (a b: α) : Decidable (a > b) := by
  simp
  apply Order.dec_eq

#print axioms Compare.dec_gt

instance Compare.dec_ge [Compare α] (a b: α) : Decidable (a >= b) := by
  simp
  apply dec_or <;> apply Order.dec_eq

#print axioms Compare.dec_gt

theorem Compare.not_lt_and_le [Compare α] {a b: α} : a < b -> b <= a -> False := by
  intro a_lt_b b_le_a
  unfold LT.lt ord_lt at a_lt_b
  simp at a_lt_b
  match b_le_a  with
  | .inl b_le_a => 
    have b_le_a := Compare.flip b_le_a
    rw [b_le_a] at a_lt_b
    contradiction
  | .inr b_eq_a =>
    rw [Compare.ord_symm _ _ b_eq_a] at a_lt_b
    contradiction

#print axioms Compare.not_lt_and_le

theorem Compare.not_lt_is_le [Compare α] {a b: α} : ¬a < b -> b <= a := fun not_lt => 
  match h:Compare.ord b a with
  | .Eq => Or.inr h
  | .Less => Or.inl h
  | .Greater => (not_lt (Compare.flip h)).elim

#print axioms Compare.not_lt_is_le

theorem Compare.not_le_is_lt [Compare α] {a b: α} : ¬a <= b -> b < a := fun not_le => 
  match h:Compare.ord b a with
  | .Less => h
  | .Eq => (not_le (Or.inr (Compare.flip h))).elim
  | .Greater => (not_le (Or.inl (Compare.flip h))).elim

#print axioms Compare.not_lt_is_le

theorem Compare.not_lt_id [Compare α] {a: α} : ¬a < a := by
  intro lt_id
  have := Compare.ord_id a
  rw [lt_id] at this
  contradiction

#print axioms Compare.not_lt_id

def Compare.le_to_eq {{ α: Sort _ }} [Compare α] (a b: α) :
  a <= b -> b <= a -> a = b := fun a_le_b b_le_a => match a_le_b with
    | .inl h => (Compare.not_lt_and_le h b_le_a).elim
    | .inr h => Compare.ord_to_eq h
      

def Nat.ord (a b: Nat) :=
  match a with
  | .zero => match b with
    | .zero => Order.Eq
    | .succ _ => Order.Greater
  | .succ a => match b with
    | .zero => Order.Less
    | .succ b => Nat.ord a b

def Nat.ord_flip (a b: Nat) : Nat.ord a b = (Nat.ord b a).flip := by
  match a with
  | .zero => match b with
    | .zero => rfl
    | .succ _ => rfl
  | .succ a => match b with
    | .zero => rfl
    | .succ b =>
      simp
      unfold ord
      simp
      rw [Nat.ord_flip a b] 
      rfl

def Nat.ord_transitive {a b c: Nat} {o: Order} : Nat.ord a b = o -> Nat.ord b c = o -> Nat.ord a c = o := by
  intro ord_ab ord_bc
  cases a <;> cases b <;> cases c
  any_goals assumption
  
  unfold ord at ord_ab ord_bc
  simp at ord_ab ord_bc
  rw [←ord_ab] at ord_bc
  contradiction
  
  unfold ord at ord_ab ord_bc
  simp at ord_ab ord_bc
  rw [←ord_ab] at ord_bc
  contradiction

  unfold ord at ord_ab ord_bc
  simp at ord_ab ord_bc
  unfold ord; simp
  apply Nat.ord_transitive ord_ab ord_bc

def Nat.ord_to_eq {a b: Nat} : Nat.ord a b = Order.Eq -> a = b := by
  intro ord_ab
  cases a <;> cases b
  rfl
  contradiction
  contradiction
  congr
  unfold ord at ord_ab
  simp at ord_ab
  exact Nat.ord_to_eq ord_ab

instance : Compare Nat where
  ord := Nat.ord

  ord_id := by
    intro a
    unfold Nat.ord
    induction a with
    | zero => simp
    | succ a' ih =>
      simp
      simp at ih
      unfold Nat.ord
      assumption
  
  ord_flip := Nat.ord_flip
  ord_transitive := Nat.ord_transitive
  ord_to_eq := Nat.ord_to_eq
