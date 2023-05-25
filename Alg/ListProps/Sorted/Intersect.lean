import Alg.ListProps.Sorted
import Alg.Nat.Add.Cmp

@[simp]
def len (list: List α) : nat := match list with
  | [] => nat.zero
  | _::xs => nat.inc (len xs)

def List.sorted_intersect.induction.bounded
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) (fuel: nat) (fuel_def: len as + len bs < fuel) : P as bs := by
  match fuel with
  | nat.zero => 
    have := (nat.not_lt_zero _) fuel_def
    contradiction
  | .inc .zero =>
    match as, bs with
    | [], [] => exact empty_left []
    | x::xs, _ =>
      have fuel_def := by
        unfold len at fuel_def
        rw [nat.add_inc_left] at fuel_def
        exact ((nat.not_lt_zero _) (nat.of_lt_inc_irr fuel_def))
      exact fuel_def.elim 
    | _, x::xs =>
      have fuel_def := by
        unfold len at fuel_def
        rw [nat.add_inc_right] at fuel_def
        exact ((nat.not_lt_zero _) (nat.of_lt_inc_irr fuel_def))
      exact fuel_def.elim
  | .inc (.inc fuel) =>
  match as with
  | [] => exact empty_left bs
  | a::as' => match bs with
    | [] => exact empty_right (a::as')
    | b::bs' => match h:Compare.ord a b with
      | .Less => 
      have := List.sorted_intersect.induction.bounded
        empty_left empty_right induct_lt induct_eq induct_gt
          as' (b::bs') fuel.inc (by
          conv at fuel_def => {
            lhs
            lhs
            unfold len
          }
          rw [nat.add_inc_left] at fuel_def
          exact fuel_def)
      apply induct_lt
      repeat assumption
      | .Eq => 
        have := (List.sorted_intersect.induction.bounded 
          empty_left empty_right induct_lt induct_eq induct_gt
          as' bs' fuel (by
          unfold len at fuel_def
          rw [nat.add_inc_right, nat.add_inc_left] at fuel_def
          exact fuel_def))
        apply induct_eq
        repeat assumption
      | .Greater =>
        have := List.sorted_intersect.induction.bounded
          empty_left empty_right induct_lt induct_eq induct_gt
          (a::as') bs' fuel.inc (by
          conv at fuel_def => {
            lhs
            rhs
            unfold len
          }
          rw [nat.add_inc_right] at fuel_def
          exact fuel_def)
        apply induct_gt
        repeat assumption

#print axioms List.sorted_intersect.induction.bounded

theorem List.sorted_intersect.induction.bounded.fuel_irr
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) (x y: nat) (x_def: len as + len bs < x) (y_def: len as + len bs < y) :
  List.sorted_intersect.induction.bounded 
    empty_left empty_right induct_lt induct_eq induct_gt as bs x x_def =
  List.sorted_intersect.induction.bounded 
    empty_left empty_right induct_lt induct_eq induct_gt as bs y y_def := by
  unfold bounded
  match x with
  | .zero =>
    have := bounded.proof_1 as bs
    contradiction
  | .inc .zero =>
    simp
    match y with
    | .zero => 
      have := bounded.proof_1 as bs
      contradiction
    | .inc .zero => rfl
    | .inc (.inc y) =>
      simp
      match as, bs with
      | [], [] =>
        rfl
      | a::as, bs =>
        have := bounded.proof_2 a as bs
        contradiction
      | as, b::bs =>
        have := bounded.proof_3 as b bs
        contradiction
  | .inc (.inc x) =>
  match y with
  | .zero =>
    have := bounded.proof_1 as bs
    contradiction
  | .inc .zero =>
    simp
    match as, bs with
    | [], [] =>
      rfl
    | a::as, bs =>
      have := bounded.proof_2 a as bs
      contradiction
    | as, b::bs =>
      have := bounded.proof_3 as b bs
      contradiction
  | .inc (.inc y) =>
  match as, bs with
  | [], _ => rfl
  | a::as, [] => rfl
  | a::as, b::bs =>
  simp
  split
  rw [bounded.fuel_irr _ _ _ _ _ _ _ x.inc y.inc]
  rw [bounded.fuel_irr _ _ _ _ _ _ _ x y]
  rw [bounded.fuel_irr _ _ _ _ _ _ _ x.inc y.inc]

#print axioms List.sorted_intersect.induction.bounded.fuel_irr

def List.sorted_intersect.induction
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) : P as bs := 
  List.sorted_intersect.induction.bounded
    empty_left empty_right induct_lt induct_eq induct_gt
    as bs (len as + len bs).inc (nat.lt_inc _)

#print axioms List.sorted_intersect.induction

theorem List.sorted_intersect.induction.unfuel
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) : 
  ∀fuel fuel_def,
  List.sorted_intersect.induction.bounded 
    empty_left empty_right induct_lt induct_eq induct_gt as bs fuel fuel_def =
  List.sorted_intersect.induction 
    empty_left empty_right induct_lt induct_eq induct_gt as bs := by
  intro fuel fuel_def
  unfold List.sorted_intersect.induction
  rw [List.sorted_intersect.induction.bounded.fuel_irr]

#print axioms List.sorted_intersect.induction.unfuel

def List.sorted_intersect [Compare α] : List α -> List α -> List α := by
  apply List.sorted_intersect.induction
  {
    intro _
    exact []
  }

  {
    intro _
    exact []
  }

  {
    intro a _ b _ _ prev
    exact prev
  }

  {
    intro a _ b _ _ prev
    exact a::prev
  }

  {
    intro a _ b _ _ prev
    exact prev
  }

#print axioms List.sorted_intersect

theorem List.sorted_intersect.empty_left [Compare α] : ∀{as bs: List α}, as = [] -> as.sorted_intersect bs = [] := by
  apply List.sorted_intersect.induction

  {
    intro bs _
    match bs with
    | [] => rfl
    | b::bs' => rfl
  }

  {
    intro _ as_is_empty
    rw [as_is_empty]
    rfl
  }

  repeat {
    intro _ _ _ _ _ _ _
    contradiction
  }

#print axioms List.sorted_intersect.empty_left

theorem List.sorted_intersect.empty_right [Compare α] : ∀{as bs: List α}, bs = [] -> as.sorted_intersect bs = [] := by
  apply List.sorted_intersect.induction


  {
    intro _ bs_is_empty
    rw [bs_is_empty]
    rfl
  }

  {
    intro as _
    match as with
    | [] => rfl
    | a::as' => rfl
  }

  repeat {
    intro _ _ _ _ _ _ _
    contradiction
  }

#print axioms List.sorted_intersect.empty_right

theorem List.sorted_intersect.induct_lt.helper [Compare α] : ∀(as bs cs ds: List α) (c d: α), as = c::cs -> bs = d::ds -> Compare.ord c d = Order.Less -> as.sorted_intersect bs = cs.sorted_intersect bs := by
  apply List.sorted_intersect.induction

  {
    intro bs
    intro cs ds c d as_eq_cs _ _
    contradiction
  }

  {
    intro as
    intro cs ds c d _ bs_eq_ds _
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds _
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    conv => {
      lhs
      unfold sorted_intersect induction induction.bounded
    }
    simp
    rw [a_ord_b]
    simp
    rw [a_eq_c, b_eq_d]
    rw [as_eq_cs, bs_eq_ds]
    simp
    rfl
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds c_lt_d
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    rw [a_eq_c, b_eq_d] at a_ord_b
    rw [c_lt_d] at a_ord_b
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds c_lt_d
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    rw [a_eq_c, b_eq_d] at a_ord_b
    rw [c_lt_d] at a_ord_b
    contradiction
  }

theorem List.sorted_intersect.induct_lt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Less -> (a::as).sorted_intersect (b::bs) = as.sorted_intersect (b::bs) := by
  intro a b as bs 
  apply List.sorted_intersect.induct_lt.helper 
  rfl
  rfl

#print axioms List.sorted_intersect.induct_lt

theorem List.sorted_intersect.induct_eq.helper [Compare α] : ∀(as bs cs ds: List α) (c d: α), as = c::cs -> bs = d::ds -> Compare.ord c d = Order.Eq -> as.sorted_intersect bs = c::(cs.sorted_intersect ds) := by
  apply List.sorted_intersect.induction

  {
    intro bs
    intro cs ds c d as_eq_cs _ _
    contradiction
  }

  {
    intro as
    intro cs ds c d _ bs_eq_ds _
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds c_lt_d
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    rw [a_eq_c, b_eq_d] at a_ord_b
    rw [c_lt_d] at a_ord_b
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds _
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    conv => {
      lhs
      unfold sorted_intersect induction induction.bounded
    }
    simp
    rw [a_ord_b]
    simp
    rw [a_eq_c, b_eq_d]
    rw [as_eq_cs, bs_eq_ds]
    simp
    unfold sorted_intersect induction
    rw [induction.bounded.fuel_irr]
    rfl
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds c_lt_d
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    rw [a_eq_c, b_eq_d] at a_ord_b
    rw [c_lt_d] at a_ord_b
    contradiction
  }

theorem List.sorted_intersect.induct_eq [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Eq -> (a::as).sorted_intersect (b::bs) = a::(as.sorted_intersect bs) := by
  intro a b as bs 
  apply List.sorted_intersect.induct_eq.helper
  rfl
  rfl

#print axioms List.sorted_intersect.induct_eq

theorem List.sorted_intersect.induct_gt.helper [Compare α] : ∀(as bs cs ds: List α) (c d: α), as = c::cs -> bs = d::ds -> Compare.ord c d = Order.Greater -> as.sorted_intersect bs = as.sorted_intersect ds := by
  apply List.sorted_intersect.induction

  {
    intro bs
    intro cs ds c d as_eq_cs _ _
    contradiction
  }

  {
    intro as
    intro cs ds c d _ bs_eq_ds _
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds c_gt_d
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    rw [a_eq_c, b_eq_d] at a_ord_b
    rw [c_gt_d] at a_ord_b
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds c_gt_d
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    rw [a_eq_c, b_eq_d] at a_ord_b
    rw [c_gt_d] at a_ord_b
    contradiction
  }

  {
    intro a as b bs a_ord_b _
    intro cs ds c d as_eq_cs bs_eq_ds _
    have ⟨ a_eq_c, as_eq_cs ⟩  := List.cons.inj as_eq_cs
    have ⟨ b_eq_d, bs_eq_ds ⟩  := List.cons.inj bs_eq_ds
    conv => {
      lhs
      unfold sorted_intersect induction induction.bounded
    }
    simp
    rw [a_ord_b]
    simp
    rw [a_eq_c, b_eq_d]
    rw [as_eq_cs, bs_eq_ds]
    simp
    unfold sorted_intersect induction
    rw [induction.bounded.fuel_irr]
    rfl
  }

theorem List.sorted_intersect.induct_gt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Greater -> (a::as).sorted_intersect (b::bs) = (a::as).sorted_intersect bs := by
  intro a b as bs 
  apply List.sorted_intersect.induct_gt.helper
  rfl
  rfl

#print axioms List.sorted_intersect.induct_gt

theorem List.sorted_intersect.contains [Compare α] : ∀(as bs: List α) (x: α),
  as.containsP x ->
  bs.containsP x ->
  as.sorted ->
  bs.sorted ->
  (as.sorted_intersect bs).containsP x := by
  apply List.sorted_intersect.induction
  {
    intro _
    intro _ _ _ _ _
    contradiction
  }
  {
    intro _
    intro _ _ _ _ _
    contradiction
  }
  {
    intro a as b bs a_ord_b prev
    intro x as_con bs_con as_sort bs_sort
    rw [induct_lt a_ord_b]
    apply prev
    match as_con with
    | .inl h =>
      simp at h
      have := List.contains_sorted bs_con bs_sort
      rw [h] at this
      have := Compare.not_lt_and_le _ _ a_ord_b
      contradiction
    | .inr _ => assumption
    assumption
    apply List.sorted.pop
    repeat assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro x as_con bs_con as_sort bs_sort
    rw [induct_eq a_ord_b]
    match as_con with
    | .inl h =>
      rw [h]
      apply Or.inl
      rfl
    | .inr h =>
      match bs_con with
      | .inl h =>
        have a_eq_b := Compare.ord_to_eq a_ord_b
        rw [a_eq_b, h]
        apply Or.inl
        rfl
      | .inr _ =>
        apply Or.inr
        apply prev
        assumption
        assumption
        apply List.sorted.pop
        assumption
        apply List.sorted.pop
        assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro x as_con bs_con as_sort bs_sort
    rw [induct_gt a_ord_b]
    apply prev
    assumption
    match bs_con with
    | .inl h =>
      simp at h
      have := List.contains_sorted as_con as_sort
      rw [h] at this
      have := Compare.not_lt_and_le _ _ (Compare.flip a_ord_b)
      contradiction
    | .inr _ => assumption
    assumption
    apply List.sorted.pop
    repeat assumption
  }

#print axioms List.sorted_intersect.contains
