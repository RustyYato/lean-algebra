import Alg.ListProps.Sorted.Induction

def List.sorted_union [Compare α] : ∀(_ _: List α), List α  := by
  apply sorted.induction
  {
    intro bs
    exact bs
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
    exact a::prev
  }
  {
    intro a _ b _ _ prev
    exact b::prev
  }

theorem List.sorted_union.empty_left [Compare α] : ∀{bs: List α}, [].sorted_union bs = bs := by
  intro bs
  apply List.sorted.empty_left

#print axioms List.sorted_union.empty_left

theorem List.sorted_union.empty_right [Compare α] : ∀{as: List α}, as.sorted_union [] = as := by
  intro as
  cases as
  rfl
  apply List.sorted.empty_right

#print axioms List.sorted_union.empty_right

theorem List.sorted_union.induct_lt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Less -> (a::as).sorted_union (b::bs) = a::(as.sorted_union (b::bs)) := by
  apply List.sorted.induct_lt

#print axioms List.sorted_union.induct_lt

theorem List.sorted_union.induct_eq [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Eq -> (a::as).sorted_union (b::bs) = a::(as.sorted_union bs) := by
  apply List.sorted.induct_eq

#print axioms List.sorted_union.induct_lt

theorem List.sorted_union.induct_gt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Greater -> (a::as).sorted_union (b::bs) = b::((a::as).sorted_union bs) := by
  apply List.sorted.induct_gt

#print axioms List.sorted_union.induct_gt

def List.sorted_union.subset_of_left [Compare α] : ∀{as bs: List α},
  as.subset_of (as.sorted_union bs) := by
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
    apply List.subset_of.push
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_gt a_ord_b]
    apply List.subset_of.push_right
    assumption
  }

#print axioms List.sorted_union.subset_of_left

def List.sorted_union.subset_of_right [Compare α] : ∀{as bs: List α},
  bs.subset_of (as.sorted_union bs) := by
  apply sorted.induction
  {
    intro bs
    rw [empty_left]
    exact List.subset_of.id
  }
  {
    intro a as
    rw [empty_right]
    exact List.subset_of.empty
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_lt a_ord_b]
    apply List.subset_of.push_right
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_eq a_ord_b]
    rw [Compare.ord_to_eq a_ord_b]
    apply List.subset_of.push
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_gt a_ord_b]
    apply List.subset_of.push
    assumption
  }

#print axioms List.sorted_union.subset_of_right

def List.sorted_union.sublist_of_left [Compare α] : ∀{as bs: List α},
  as.sublist_of (as.sorted_union bs) := by
  apply sorted.induction
  {
    intro bs
    rw [empty_left]
    apply List.sublist_of.empty
  }
  {
    intro a as
    rw [empty_right]
    exact List.sublist_of.id
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_lt a_ord_b]
    apply Or.inl
    apply And.intro
    rfl
    apply prev
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_eq a_ord_b]
    apply Or.inl
    apply And.intro
    rfl
    apply prev
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_gt a_ord_b]
    apply Or.inr
    apply prev
  }

#print axioms List.sorted_union.sublist_of_left

def List.sorted_union.sublist_of_right [Compare α] : ∀{as bs: List α},
  bs.sublist_of (as.sorted_union bs) := by
  apply sorted.induction
  {
    intro bs
    rw [empty_left]
    apply List.sublist_of.id
  }
  {
    intro a as
    rw [empty_right]
    exact List.sublist_of.empty
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_lt a_ord_b]
    apply Or.inr
    apply prev
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_eq a_ord_b]
    rw [Compare.ord_to_eq a_ord_b]
    apply Or.inl
    apply And.intro
    rfl
    apply prev
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_gt a_ord_b]
    apply Or.inl
    apply And.intro
    rfl
    apply prev
  }

#print axioms List.sorted_union.sublist_of_right

theorem List.sorted_union.keeps_sorted.helper [Compare α] {x: α} : 
  ∀ {as bs},
  sorted (x::as) ->
  sorted (x::bs) ->
  sorted (sorted_union as bs) ->
  sorted (x :: sorted_union as bs) := by
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
    intro a as b bs a_ord_b _
    intro as_sort _ i_sort
    rw [induct_eq a_ord_b]
    rw [induct_eq a_ord_b] at i_sort
    apply And.intro
    exact as_sort.left
    assumption
  }
  {
    intro a as b bs a_ord_b _
    intro _ bs_sort i_sort
    rw [induct_gt a_ord_b]
    rw [induct_gt a_ord_b] at i_sort
    apply And.intro
    exact bs_sort.left
    assumption
  }

#print axioms List.sorted_union.keeps_sorted.helper

def List.sorted_union.keeps_sorted [Compare α] : ∀{as bs: List α},
  as.sorted ->
  bs.sorted ->
  (as.sorted_union bs).sorted := by
  apply sorted.induction
  {
    intro bs
    intro _ _
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
    have a_eq_b : a = b := Compare.ord_to_eq a_ord_b
    rw [induct_eq a_ord_b]
    apply keeps_sorted.helper
    assumption
    rw [a_eq_b]
    assumption
    apply prev
    exact as_sort.pop
    exact bs_sort.pop
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [induct_gt a_ord_b]
    apply keeps_sorted.helper
    apply And.intro
    apply Or.inl
    exact Compare.flip a_ord_b
    assumption
    assumption
    apply prev
    assumption
    exact bs_sort.pop
  }

#print axioms List.sorted_union.keeps_sorted
