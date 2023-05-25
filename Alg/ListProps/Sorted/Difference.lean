import Alg.ListProps.Sorted.Induction

def List.sorted_difference [Compare α] : ∀(_ _: List α), List α  := by
  apply sorted.induction
  {
    intro _
    exact []
  }
  {
    intro a as
    exact a::as
  }
  {
    intro a _ b _ _ prev
    exact a::prev
  }
  {
    intro a _ b _ _ prev
    exact prev
  }
  {
    intro a _ b _ _ prev
    exact prev
  }

theorem List.sorted_difference.empty_left [Compare α] : ∀{bs: List α}, [].sorted_difference bs = [] := by
  intro bs
  apply List.sorted.empty_left

#print axioms List.sorted_difference.empty_left

theorem List.sorted_difference.empty_right [Compare α] : ∀{as: List α}, as.sorted_difference [] = as := by
  intro as
  cases as
  rfl
  apply List.sorted.empty_right

#print axioms List.sorted_difference.empty_right

theorem List.sorted_difference.induct_lt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Less -> (a::as).sorted_difference (b::bs) = a::(as.sorted_difference (b::bs)) := by
  apply List.sorted.induct_lt

#print axioms List.sorted_difference.induct_lt

theorem List.sorted_difference.induct_eq [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Eq -> (a::as).sorted_difference (b::bs) = as.sorted_difference bs := by
  apply List.sorted.induct_eq

#print axioms List.sorted_difference.induct_lt

theorem List.sorted_difference.induct_gt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Greater -> (a::as).sorted_difference (b::bs) = (a::as).sorted_difference bs := by
  apply List.sorted.induct_gt

#print axioms List.sorted_difference.induct_gt

