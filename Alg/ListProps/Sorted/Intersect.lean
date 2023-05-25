import Alg.ListProps.Sorted.Induction

def List.sorted_intersect [Compare α] : List α -> List α -> List α := by
  apply List.sorted.induction
  {
    intro _
    exact []
  }

  {
    intro _ _
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

theorem List.sorted_intersect.empty_left [Compare α] : ∀{bs: List α}, [].sorted_intersect bs = [] := by
  intro bs
  apply List.sorted.empty_left

#print axioms List.sorted_intersect.empty_left

theorem List.sorted_intersect.empty_right [Compare α] : ∀{a: α} {as: List α}, (a::as).sorted_intersect [] = [] := by
  intro a as
  apply List.sorted.empty_right

#print axioms List.sorted_intersect.empty_right

theorem List.sorted_intersect.induct_lt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Less -> (a::as).sorted_intersect (b::bs) = as.sorted_intersect (b::bs) := by
  apply List.sorted.induct_lt

#print axioms List.sorted_intersect.induct_lt

theorem List.sorted_intersect.induct_eq [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Eq -> (a::as).sorted_intersect (b::bs) = a::(as.sorted_intersect bs) := by
  apply List.sorted.induct_eq

#print axioms List.sorted_intersect.induct_lt

theorem List.sorted_intersect.induct_gt [Compare α] : ∀{a b: α} {as bs: List α}, Compare.ord a b = Order.Greater -> (a::as).sorted_intersect (b::bs) = (a::as).sorted_intersect bs := by
  apply List.sorted.induct_gt

#print axioms List.sorted_intersect.induct_gt

theorem List.sorted_intersect.keeps_sorted.helper [Compare α] {x: α} : 
  ∀ {as bs},
  sorted (x::as) ->
  sorted (x::bs) ->
  sorted (sorted_intersect as bs) ->
  sorted (x :: sorted_intersect as bs) := by
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
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort i_sort
    rw [induct_lt a_ord_b]
    rw [induct_lt a_ord_b] at i_sort
    apply prev
    exact as_sort.pop_snd
    assumption
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
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort i_sort
    rw [induct_gt a_ord_b]
    rw [induct_gt a_ord_b] at i_sort
    apply prev
    assumption
    exact bs_sort.pop_snd
    assumption
  }

theorem List.sorted_intersect.keeps_sorted [Compare α] : ∀(as bs: List α),
  as.sorted ->
  bs.sorted ->
  (as.sorted_intersect bs).sorted := by
  apply List.sorted.induction
  {
    intro _
    intro _ _
    rw [empty_left]
    assumption
  }
  {
    intro _ _
    intro _ _
    rw [empty_right]
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [induct_lt a_ord_b]
    apply prev
    exact as_sort.pop
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [induct_eq a_ord_b]
    apply keeps_sorted.helper
    assumption
    rw [Compare.ord_to_eq a_ord_b]
    assumption
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

#print axioms List.sorted_intersect.keeps_sorted

theorem List.sorted_intersect.of_contains [Compare α] : ∀(as bs: List α) (x: α),
  as.containsP x ->
  bs.containsP x ->
  as.sorted ->
  bs.sorted ->
  (as.sorted_intersect bs).containsP x := by
  apply List.sorted.induction
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

#print axioms List.sorted_intersect.of_contains

theorem List.sorted_intersect.to_contains [Compare α] : ∀(as bs: List α) (x: α),
  as.sorted ->
  bs.sorted ->
  (as.sorted_intersect bs).containsP x ->
  as.containsP x ∧ bs.containsP x 
   := by
  apply List.sorted.induction
  {
    intro _
    intro _ _ _ i_con
    rw [empty_left] at i_con
    contradiction
  }
  {
    intro _ _
    intro _ _ _ i_con
    rw [empty_right] at i_con
    contradiction
  }
  {
    intro a as b bs a_ord_b prev
    intro x as_sort bs_sort i_con
    rw [induct_lt a_ord_b] at i_con
    have ⟨ a_con, b_con ⟩  := prev x as_sort.pop bs_sort i_con
    apply And.intro
    apply Or.inr
    repeat assumption
  }
  {
    intro a as b bs a_ord_b prev
    intro x as_sort bs_sort i_con
    rw [induct_eq a_ord_b] at i_con
    match i_con with
    | .inl found =>
      apply And.intro <;> apply Or.inl
      exact found
      rw [←Compare.ord_to_eq a_ord_b]
      exact found
    | .inr i_con =>
    have ⟨ a_con, b_con ⟩  := prev x as_sort.pop bs_sort.pop i_con
    apply And.intro <;> (apply Or.inr; assumption)
  }
  {
    intro a as b bs a_ord_b prev
    intro x as_sort bs_sort i_con
    rw [induct_gt a_ord_b] at i_con
    have ⟨ a_con, b_con ⟩  := prev x as_sort bs_sort.pop i_con
    apply And.intro
    assumption
    apply Or.inr
    assumption
  }

#print axioms List.sorted_intersect.to_contains
