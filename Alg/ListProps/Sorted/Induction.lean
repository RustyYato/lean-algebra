import Alg.ListProps.Sorted
import Alg.Nat.Add.Cmp

@[simp]
def len (list: List α) : nat := match list with
  | [] => nat.zero
  | _::xs => nat.inc (len xs)

def List.sorted.induction.bounded
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
      have := List.sorted.induction.bounded
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
        have := (List.sorted.induction.bounded 
          empty_left empty_right induct_lt induct_eq induct_gt
          as' bs' fuel (by
          unfold len at fuel_def
          rw [nat.add_inc_right, nat.add_inc_left] at fuel_def
          exact fuel_def))
        apply induct_eq
        repeat assumption
      | .Greater =>
        have := List.sorted.induction.bounded
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

#print axioms List.sorted.induction.bounded

theorem List.sorted.induction.bounded.fuel_irr
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) (x y: nat) (x_def: len as + len bs < x) (y_def: len as + len bs < y) :
  List.sorted.induction.bounded 
    empty_left empty_right induct_lt induct_eq induct_gt as bs x x_def =
  List.sorted.induction.bounded 
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

#print axioms List.sorted.induction.bounded.fuel_irr

def List.sorted.induction
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) : P as bs := 
  List.sorted.induction.bounded
    empty_left empty_right induct_lt induct_eq induct_gt
    as bs (len as + len bs).inc (nat.lt_inc _)

#print axioms List.sorted.induction

theorem List.sorted.induction.unfuel
  [Compare α] 
  {P: List α -> List α -> Sort _}
  (empty_left: ∀bs, P [] bs)
  (empty_right: ∀as, P as [])
  (induct_lt: ∀a as b bs, Compare.ord a b = Order.Less -> P as (b::bs) -> P (a::as) (b::bs))
  (induct_eq: ∀a as b bs, Compare.ord a b = Order.Eq -> P as bs -> P (a::as) (b::bs))
  (induct_gt: ∀a as b bs, Compare.ord a b = Order.Greater -> P (a::as) bs -> P (a::as) (b::bs))
  (as bs: List α) : 
  ∀fuel fuel_def,
  List.sorted.induction.bounded 
    empty_left empty_right induct_lt induct_eq induct_gt as bs fuel fuel_def =
  List.sorted.induction 
    empty_left empty_right induct_lt induct_eq induct_gt as bs := by
  intro fuel fuel_def
  unfold List.sorted.induction
  rw [List.sorted.induction.bounded.fuel_irr]

#print axioms List.sorted.induction.unfuel
