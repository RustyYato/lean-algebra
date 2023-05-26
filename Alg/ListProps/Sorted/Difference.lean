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

def List.sorted_difference.subset_of [Compare α] : ∀{as bs: List α},
  (as.sorted_difference bs).subset_of as := by
  apply sorted.induction
  {
    intro bs
    rw [empty_left]
    exact List.subset_of.empty
  }
  {
    intro a as
    rw [empty_right]
    exact List.subset_of.id
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_lt a_ord_b]
    apply List.subset_of.push
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_eq a_ord_b]
    apply List.subset_of.push_right
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_gt a_ord_b]
    assumption
  }

theorem List.sorted_difference.keeps_sorted.helper [Compare α] {x: α} : 
  ∀ {as bs},
  sorted (x::as) ->
  sorted (x::bs) ->
  sorted (sorted_difference as bs) ->
  sorted (x :: sorted_difference as bs) := by
  apply sorted.induction
  {
    intro _
    intro _ _ _
    rw [empty_left]
    assumption
  }
  {
    intro _ _
    intro _ _ _
    rw [empty_right]
    assumption
  }
  {
    intro a as b bs a_ord_b _
    intro as_sort _ i_sort
    rw [induct_lt a_ord_b]
    rw [induct_lt a_ord_b] at i_sort
    apply And.intro
    exact as_sort.left
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort i_sort
    rw [induct_eq a_ord_b]
    rw [induct_eq a_ord_b] at i_sort
    apply prev
    exact as_sort.pop_snd
    exact bs_sort.pop_snd
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort i_sort
    rw [induct_gt a_ord_b]
    rw [induct_gt a_ord_b] at i_sort
    apply prev
    assumption
    exact bs_sort.pop_snd
    assumption
  }

def List.sorted_difference.keeps_sorted [Compare α] : ∀{as bs: List α},
  as.sorted ->
  bs.sorted ->
  (as.sorted_difference bs).sorted := by
  apply sorted.induction
  {
    intro bs
    intro as_sort _
    rw [empty_left]
    assumption
  }
  {
    intro a as
    intro as_sort _
    rw [empty_right]
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [induct_lt a_ord_b]
    apply keeps_sorted.helper
    assumption
    apply And.intro
    apply Or.inl
    assumption
    assumption
    apply prev
    exact as_sort.pop
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [induct_eq a_ord_b]
    apply prev
    exact as_sort.pop
    exact bs_sort.pop
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [induct_gt a_ord_b]
    apply prev
    assumption
    exact bs_sort.pop
  }
