import Alg.ListProps.Sorted.Induction

def List.sorted_merge [Compare α] (as bs: List α) := by
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
    exact a::b::prev
  }
  {
    intro a _ b _ _ prev
    exact b::prev
  }

theorem List.sorted_merge.empty_left [Compare α] : ∀{bs: List α}, [].sorted_merge bs = bs := by
  intro bs
  apply List.sorted.empty_left

#print axioms List.sorted_merge.empty_left

theorem List.sorted_merge.empty_right [Compare α] : ∀{as: List α}, as.sorted_merge [] = as := by
  intro as
  cases as
  rfl
  apply List.sorted.empty_right

#print axioms List.sorted_merge.empty_right

theorem List.sorted_merge.induct_lt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Less -> (a::as).sorted_merge (b::bs) = a::(as.sorted_merge (b::bs)) := by
  apply List.sorted.induct_lt

#print axioms List.sorted_merge.induct_lt

theorem List.sorted_merge.induct_eq [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Eq -> (a::as).sorted_merge (b::bs) = a::b::(as.sorted_merge bs) := by
  apply List.sorted.induct_eq

#print axioms List.sorted_merge.induct_lt

theorem List.sorted_merge.induct_gt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Greater -> (a::as).sorted_merge (b::bs) = b::((a::as).sorted_merge bs) := by
  apply List.sorted.induct_gt

#print axioms List.sorted_merge.induct_gt

theorem List.sorted_merge.keeps_sorted.helper [Compare α] {x: α} : 
  ∀ {as bs},
  sorted (x::as) ->
  sorted (x::bs) ->
  sorted (sorted_merge as bs) ->
  sorted (x :: sorted_merge as bs) := by
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

theorem List.sorted_merge.keeps_sorted [Compare α] : ∀(as bs: List α), as.sorted -> bs.sorted -> (as.sorted_merge bs).sorted := by
    apply sorted.induction
    {
      intro bss
      intro _ _
      rw [empty_left]
      assumption
    }
    {
      intro a as
      intro _ _
      rw [empty_right]
      assumption
    }
    {
      intro a as b bs a_ord_b prev
      intro as_sort bs_sort
      rw [induct_lt a_ord_b]
      apply List.sorted_merge.keeps_sorted.helper
      any_goals assumption
      apply And.intro
      apply Or.inl
      exact a_ord_b
      assumption
      apply prev
      exact as_sort.pop
      assumption
    }
    {
      intro a as b bs a_ord_b prev
      intro as_sort bs_sort
      rw [induct_eq a_ord_b]
      apply And.intro
      apply Or.inr
      assumption
      apply List.sorted_merge.keeps_sorted.helper
      any_goals assumption
      rw [←(Compare.ord_to_eq a_ord_b)]
      assumption
      apply prev
      exact as_sort.pop
      exact bs_sort.pop
    }
    {
      intro a as b bs a_ord_b prev
      intro as_sort bs_sort
      rw [induct_gt a_ord_b]
      apply List.sorted_merge.keeps_sorted.helper
      any_goals assumption
      apply And.intro
      apply Or.inl
      exact Compare.flip a_ord_b
      assumption
      apply prev
      assumption
      exact bs_sort.pop
    }
    repeat admit

#print axioms List.sorted_merge.keeps_sorted

theorem List.sorted_merge.keeps_allP {P: α -> Prop} [Compare α] : ∀{as bs: List α}, as.allP P -> bs.allP P -> (as.sorted_merge bs).allP P := by
    apply sorted.induction
    {
      intro bs
      intro _ bs_all
      rw [empty_left]
      assumption
    }
    {
      intro a as
      intro as_all _
      rw [empty_right]
      assumption
    }
    {
      intro a as b bs a_ord_b prev
      intro as_all bs_all
      rw [induct_lt a_ord_b]
      apply And.intro
      exact as_all.left
      apply prev
      exact as_all.right
      assumption
    }
    {
      intro a as b bs a_ord_b prev
      intro as_all bs_all
      rw [induct_eq a_ord_b]
      apply And.intro
      exact as_all.left
      apply And.intro
      exact bs_all.left
      apply prev
      exact as_all.right
      exact bs_all.right
    }
    {
      intro a as b bs a_ord_b prev
      intro as_all bs_all
      rw [induct_gt a_ord_b]
      apply And.intro
      exact bs_all.left
      apply prev
      assumption
      exact bs_all.right
    }

#print axioms List.sorted_merge.keeps_allP

theorem List.sorted_merge.keeps_anyP {P: α -> Prop} [Compare α] : ∀{as bs: List α}, as.anyP P ∨ bs.anyP P -> (as.sorted_merge bs).anyP P := by
    apply sorted.induction
    {
      intro bs
      intro as_or_bs
      rw [empty_left]
      match as_or_bs with
      | .inl _ => contradiction
      | .inr _ => assumption
    }
    {
      intro a as
      intro as_or_bs
      rw [empty_right]
      match as_or_bs with
      | .inl _ => assumption
      | .inr _ => contradiction
    }
    {
      intro a as b bs a_ord_b prev
      intro as_or_bs
      rw [induct_lt a_ord_b]
      match as_or_bs with
      | .inl (.inl _) =>
        apply Or.inl
        assumption
      | .inl (.inr _) =>
        apply Or.inr
        apply prev
        apply Or.inl
        assumption
      | .inr _ =>
        apply Or.inr
        apply prev
        apply Or.inr
        assumption
    }
    {
      intro a as b bs a_ord_b prev
      intro as_or_bs
      rw [induct_eq a_ord_b]
      match as_or_bs with
      | .inl (.inl _) =>
        apply Or.inl
        assumption
      | .inl (.inr _) =>
        apply Or.inr
        apply Or.inr
        apply prev
        apply Or.inl
        assumption
      | .inr (.inl _) =>
        apply Or.inl
        rw [Compare.ord_to_eq a_ord_b]
        assumption
      | .inr (.inr _) =>
        apply Or.inr
        apply Or.inr
        apply prev
        apply Or.inr
        assumption
    }
    {
      intro a as b bs a_ord_b prev
      intro as_or_bs
      rw [induct_gt a_ord_b]
      match as_or_bs with
      | .inr (.inl _) =>
        apply Or.inl
        assumption
      | .inr (.inr _) =>
        apply Or.inr
        apply prev
        apply Or.inr
        assumption
      | .inl _ =>
        apply Or.inr
        apply prev
        apply Or.inl
        assumption
    }

#print axioms List.sorted_merge.keeps_anyP

def List.sorted_merge.contains [Compare α] (as bs: List α) (x: α) : as.containsP x ∨ bs.containsP x -> (as.sorted_merge bs).containsP x := by
    unfold containsP
    apply List.sorted_merge.keeps_anyP

#print axioms List.sorted_merge.contains

def List.sorted_merge.src_left_sublist [Compare α] {as bs: List α} :
  as.sublist_of (as.sorted_merge bs) := by
  intro x con
  exact List.sorted_merge.contains as bs x (Or.inl con)

#print axioms List.sorted_merge.src_left_sublist

def List.sorted_merge.src_right_sublist [Compare α] {as bs: List α} :
  bs.sublist_of (as.sorted_merge bs) := by
  intro x con
  exact List.sorted_merge.contains as bs x (Or.inr con)

#print axioms List.sorted_merge.src_right_sublist
