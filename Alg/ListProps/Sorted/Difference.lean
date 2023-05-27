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

#print axioms List.sorted_difference.subset_of

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

#print axioms List.sorted_difference.keeps_sorted

def List.sorted_difference.sublist_of_left [Compare α] : ∀{as bs: List α},
  (as.sorted_difference bs).sublist_of as := by
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
    apply List.sublist_of.push
    assumption
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_eq a_ord_b]
    apply List.sublist_of.push_right prev
  }
  {
    intro a as b bs a_ord_b prev
    rw [induct_gt a_ord_b]
    assumption
  }

#print axioms List.sorted_difference.sublist_of_left

def List.sorted_difference.not_in_left [Compare α] : ∀{as bs: List α},
  bs.sorted ->
  bs = c::cs ->
  ¬as.containsP c ->
  as.sorted_difference bs = as.sorted_difference cs := by
  apply sorted.induction
  {
    intro bs
    intro _ _ _
    rw [empty_left, empty_left]
  }
  {
    intro bs
    intro b_sort _ not_con
    contradiction
  }
  {
    intro a as b bs a_ord_b prev
    intro b_sort bs_eq_cs not_con
    rw [induct_lt a_ord_b]
    have := prev b_sort bs_eq_cs (by
        intro con
        apply not_con
        apply Or.inr
        assumption)
    rw [this]
    match cs with
    | [] =>
      rw [empty_right, empty_right]
    | c'::cs =>
      rw [induct_lt]
      rw [(List.cons.inj bs_eq_cs).left] at a_ord_b
      rw [bs_eq_cs] at b_sort
      exact Compare.lt_le_trans a_ord_b b_sort.left
  }
  {
    intro a as b bs a_ord_b prev
    intro b_sort bs_eq_cs not_con
    rw [(List.cons.inj bs_eq_cs).left] at a_ord_b
    rw [Compare.ord_to_eq a_ord_b] at not_con
    have := not_con (Or.inl rfl)
    contradiction
  }
  {
    intro a as b bs a_ord_b _
    intro _ bs_eq_cs _
    rw [induct_gt a_ord_b]
    rw [(List.cons.inj bs_eq_cs).right]
  }

def List.sorted_difference.not_in_right [Compare α] : ∀{as bs: List α},
  as.sorted ->
  bs.sorted ->
  as = c::cs ->
  ¬bs.containsP c ->
  as.sorted_difference bs = c::(cs.sorted_difference bs) := by
  apply sorted.induction
  {
    intro bs
    intro _ _ a_eq_c _
    rw [empty_left]
    contradiction
  }
  {
    intro a as
    intro _ _ a_eq_c _
    rw [empty_right]
    rw [empty_right]
    rw [a_eq_c]
  }
  {
    intro a as b bs a_ord_b _
    intro _ _ a_eq_c _
    rw [induct_lt a_ord_b]
    have ⟨ a_eq_c, as_eq_cs ⟩ := List.cons.inj a_eq_c
    rw [a_eq_c]
    congr
  }
  {
    intro a as b bs a_ord_b _
    intro _ _ a_eq_c not_con
    rw [induct_eq a_ord_b]
    have ⟨ a_eq_c, as_eq_cs ⟩ := List.cons.inj a_eq_c
    have := Compare.ord_to_eq a_ord_b
    rw [a_eq_c.symm.trans this] at not_con
    have := not_con (Or.inl rfl)
    contradiction
  }
  {
    intro a as b bs a_ord_b prev
    intro a_sort b_sort as_eq_cs not_con
    rw [induct_gt a_ord_b]
    rw [prev a_sort b_sort.pop as_eq_cs]
    {
      rw [←List.sorted_difference.not_in_left]
      exact b_sort
      rfl
      have := a_sort.pop
      have ⟨ _, as_eq_cs ⟩  := List.cons.inj as_eq_cs
      rw [←as_eq_cs]
      match as with
      | [] =>
        intro; contradiction
      | a'::as =>
      apply (a_sort.pop).not_contains
      apply Compare.lt_le_trans (Compare.flip a_ord_b)
      exact a_sort.left
    }
    intro con_tail
    apply not_con
    apply Or.inr
    assumption
  }

#print axioms List.sorted_difference.not_in_right

def List.sorted_difference.all_not_in_right [Compare α] : ∀{as bs: List α},
  as.sorted ->
  bs.sorted ->
  as = cs ++ ds ->
  cs.allP (fun c => ¬bs.containsP c) ->
  as.sorted_difference bs = cs ++ (ds.sorted_difference bs) := by
  induction cs with
  | nil =>
    intro as bs _ _ as_eq_cs_ds all_cs_not_in_bs
    rw [List.nil_append] at as_eq_cs_ds
    rw [List.nil_append, as_eq_cs_ds]
  | cons c cs ih =>
    intro as bs as_sorted bs_sorted as_eq_cs_ds all_cs_not_in_bs
    match as with
    | a::as =>
    have ⟨ a_eq_c, as_eq_cs_ds ⟩ := List.cons.inj as_eq_cs_ds
    have := ih as_sorted.pop bs_sorted as_eq_cs_ds all_cs_not_in_bs.right
    rw [@left_concat_eq_append _ c, _append_assoc, ←left_concat_eq_append]
    rw [←this]
    have c_not_in_bs := all_cs_not_in_bs.left
    rw [←a_eq_c] at *
    apply List.sorted_difference.not_in_right _ _ rfl
    any_goals assumption

#print axioms List.sorted_difference.all_not_in_right

