import Alg.ListProps.Sorted.Merge
import Alg.ListProps.Sorted.Intersect
import Alg.ListProps.Sorted.Union
import Alg.ListProps.Sorted.Difference
import Alg.Basic

theorem all_eq_to_end :
  xs.allP (fun i => i = x) ->
  x::xs = xs ++ [x] := by
  intro all_eq_first
  match xs with
  | [] => rw [List.nil_append]
  | x'::xs =>
  rw [all_eq_first.left]
  congr
  apply all_eq_to_end all_eq_first.right

#print axioms all_eq_to_end

theorem all_eq_to_sorted [Compare α] {xs: List α} :
  xs.allP (fun i => i = x) ->
  xs.sorted := by
  intro all_eq_first
  match xs with
  | [] | [_] => trivial
  | a::b::xs =>
  apply And.intro
  rw [all_eq_first.left, all_eq_first.right.left]
  apply Compare.le_id
  apply all_eq_to_sorted all_eq_first.right

#print axioms all_eq_to_sorted

theorem List.sorted.union_def.helper [Compare α]: 
  ∀{as bs: List α} (x: α) (xs: List α), 
  xs.allP (fun i => i = x) ->
  (x::as).sorted ->
  (x::bs).sorted ->
  xs ++ (List.sorted_union as bs) = List.sorted_difference (xs ++ List.sorted_merge as bs) (List.sorted_intersect as bs) := by
  apply sorted.induction
  {
    intro bs
    intro x xs _ _ _
    rw [
      sorted_union.empty_left,
      sorted_merge.empty_left,
      sorted_intersect.empty_left,
      sorted_difference.empty_right,
    ]
  }
  {
    intro a as
    intro x xs _ _ _
    rw [
      sorted_union.empty_right,
      sorted_merge.empty_right,
      sorted_intersect.empty_right,
      sorted_difference.empty_right,
    ]
  }
  {
    intro a as b bs a_ord_b prev
    intro x xs xs_eq_x as_sort bs_sort
    rw [
      sorted_merge.induct_lt a_ord_b,
      sorted_intersect.induct_lt a_ord_b,
      sorted_union.induct_lt a_ord_b,
    ]
    have prev_empty := @prev x [] True.intro as_sort.pop_snd bs_sort
    rw [List.nil_append, List.nil_append] at prev_empty
    rw [prev_empty]
    
    have : ¬containsP (sorted_intersect as (b :: bs)) a := by
      apply contrapositive (List.sorted_intersect.to_contains _ _ a (as_sort.pop).pop bs_sort.pop)
      intro con_and_con
      have ⟨ _, bs_con_a ⟩ := con_and_con
      have := (bs_sort.pop).not_contains a_ord_b
      contradiction
    have : ¬containsP (sorted_intersect as (b :: bs)) x := by
      apply contrapositive (List.sorted_intersect.to_contains _ _ x (as_sort.pop).pop bs_sort.pop)
      intro con_and_con
      have ⟨ _, bs_con_a ⟩ := con_and_con
      apply (bs_sort.pop).not_contains (Compare.le_lt_trans as_sort.left a_ord_b)
      assumption
    have : sorted (a :: sorted_merge as (b :: bs)) := by
      apply List.sorted_merge.keeps_sorted.helper
      exact as_sort.pop
      apply And.intro
      exact Or.inl a_ord_b
      exact bs_sort.pop
      apply List.sorted_merge.keeps_sorted
      exact (as_sort.pop).pop
      exact bs_sort.pop
    have : sorted (sorted_intersect as (b :: bs)) := by
      apply List.sorted_intersect.keeps_sorted
      exact (as_sort.pop).pop
      exact bs_sort.pop
    
    rw [List.sorted_difference.all_not_in_right _ _ rfl]
    rw [List.sorted_difference.not_in_right _ _ rfl]
    any_goals assumption
    apply xs_eq_x.map
    intro y y_eq_x
    rw [y_eq_x]
    assumption
    
    match xs with
    | [] =>
      rw [List.nil_append]
      assumption
    | x'::xs =>
    apply List.sorted.append
    apply all_eq_to_sorted xs_eq_x
    assumption
    have to_end_append : x'::xs = xs ++ [x'] := by
      apply all_eq_to_end
      apply xs_eq_x.right.map
      intro i i_eq_x
      rw [i_eq_x]
      exact xs_eq_x.left.symm
    exact to_end_append
    rfl
    rw [xs_eq_x.left]
    exact as_sort.left
  }
  {
    intro a as b bs a_ord_b prev
    intro x xs xs_eq_x as_sort bs_sort
    have a_eq_b := Compare.ord_to_eq a_ord_b
    rw [sorted_merge.induct_eq a_ord_b] at *
    have a_ord_x := decEq (Compare.ord a x) .Eq
    have b_ord_x := decEq (Compare.ord b x) .Eq
    match dec_and a_ord_x b_ord_x with
    | .isTrue ⟨ a_ord_x, b_ord_x ⟩  =>
      rw [Compare.ord_to_eq a_ord_x, Compare.ord_to_eq b_ord_x]
      rw [sorted_intersect.induct_eq (Compare.ord_id _)] at *
      rw [_append_cons, ←all_eq_to_end, List.cons_append]
      rw [_append_cons, ←all_eq_to_end, List.cons_append]
      rw [sorted_difference.induct_eq (Compare.ord_id _)] at *
      rw [sorted_union.induct_eq (Compare.ord_id _)] at *
      rw [_append_cons, ←all_eq_to_end]
      rw [←List.cons_append]
      rw [@prev x (x::xs) (⟨ rfl , xs_eq_x ⟩) as_sort.pop_snd bs_sort.pop_snd]
      assumption
      assumption
      assumption
    | .isFalse not_and_ord => 
    rw [List.sorted_difference.all_not_in_right _ _ rfl]
    congr

    {
      rw [List.sorted_intersect.induct_eq a_ord_b]
      rw [List.sorted_union.induct_eq a_ord_b]
      rw [List.sorted_difference.induct_eq (Compare.ord_id _)]
      have prev_empty := @prev a [a] (⟨rfl ,True.intro⟩) as_sort.pop (by
        rw [a_eq_b]
        exact bs_sort.pop)
      rw [List.cons_append, List.cons_append, List.nil_append, List.nil_append] at prev_empty
      rw [←a_eq_b]
      assumption
    }
    
    {
      apply xs_eq_x.map
      intro x' x'_eq_x
      rw [x'_eq_x]
      intro con
      have := List.sorted_intersect.sublist_of_left (a::as) (b::bs)
      have := (as_sort.pop).contains (this.containsP con)
      have x_eq_a := Compare.le_to_eq _ _ as_sort.left this

      have := List.sorted_intersect.sublist_of_right (a::as) (b::bs)
      have := (bs_sort.pop).contains (this.containsP con)
      have x_eq_b := Compare.le_to_eq _ _ bs_sort.left this

      rw [←x_eq_a, ←x_eq_b] at not_and_ord
      exact not_and_ord ⟨ Compare.ord_id _, Compare.ord_id _ ⟩
    }
    {
      have : sorted (a :: b :: sorted_merge as bs) := by
        repeat any_goals apply And.intro
        exact Or.inr a_ord_b
        apply List.sorted_merge.keeps_sorted.helper
        rw [←a_eq_b]
        exact as_sort.pop
        exact bs_sort.pop
        apply List.sorted_merge.keeps_sorted
        exact (as_sort.pop).pop
        exact (bs_sort.pop).pop
      match xs with
      | [] => rw [List.nil_append]; assumption
      | x'::xs =>
        rw [all_eq_to_end]
        {
          apply sorted.append
          rw [←all_eq_to_end]
          apply all_eq_to_sorted xs_eq_x
          apply xs_eq_x.right.map
          intro i i_eq_x
          apply i_eq_x.trans
          exact xs_eq_x.left.symm
          assumption
          rfl
          rfl
          rw [xs_eq_x.left]
          exact as_sort.left
        }
        apply xs_eq_x.right.map
        intro i i_eq_x
        apply i_eq_x.trans
        exact xs_eq_x.left.symm
    }
    {
      apply List.sorted_intersect.keeps_sorted
      exact as_sort.pop
      exact bs_sort.pop
    }
  }
  {
    intro a as b bs a_ord_b prev
    intro x xs xs_eq_x as_sort bs_sort
    have b_ord_a := Compare.flip a_ord_b
    rw [
      sorted_merge.induct_gt a_ord_b,
      sorted_intersect.induct_gt a_ord_b,
      sorted_union.induct_gt a_ord_b,
    ]
    have prev_empty := @prev x [] True.intro as_sort bs_sort.pop_snd
    rw [List.nil_append, List.nil_append] at prev_empty
    rw [prev_empty]
    clear prev
    
    have : ¬containsP (sorted_intersect (a :: as) bs) b := by
      apply contrapositive (List.sorted_intersect.to_contains _ _ b as_sort.pop (bs_sort.pop).pop)
      intro con_and_con
      have ⟨ as_con_a, _ ⟩ := con_and_con
      have := (as_sort.pop).not_contains b_ord_a
      contradiction
    have : ¬containsP (sorted_intersect (a :: as) bs) x := by
      apply contrapositive (List.sorted_intersect.to_contains _ _ x as_sort.pop (bs_sort.pop).pop)
      intro con_and_con
      have ⟨ as_con_a, _ ⟩ := con_and_con
      apply (as_sort.pop).not_contains (Compare.le_lt_trans bs_sort.left b_ord_a)
      assumption
    have : sorted (b :: sorted_merge (a :: as) bs) := by
      apply List.sorted_merge.keeps_sorted.helper
      apply And.intro
      exact Or.inl b_ord_a
      exact as_sort.pop
      exact bs_sort.pop
      apply List.sorted_merge.keeps_sorted
      exact as_sort.pop
      exact (bs_sort.pop).pop
    have : sorted (sorted_intersect (a :: as) bs) := by
      apply List.sorted_intersect.keeps_sorted
      exact as_sort.pop
      exact (bs_sort.pop).pop

    rw [List.sorted_difference.all_not_in_right _ _ rfl]
    rw [List.sorted_difference.not_in_right _ _ rfl]
    any_goals assumption
    apply xs_eq_x.map
    intro y y_eq_x
    rw [y_eq_x]
    assumption
    
    match xs with
    | [] =>
      rw [List.nil_append]
      assumption
    | x'::xs =>
    apply List.sorted.append
    apply all_eq_to_sorted xs_eq_x
    assumption
    have to_end_append : x'::xs = xs ++ [x'] := by
      apply all_eq_to_end
      apply xs_eq_x.right.map
      intro i i_eq_x
      rw [i_eq_x]
      exact xs_eq_x.left.symm
    exact to_end_append
    rfl
    rw [xs_eq_x.left]
    exact bs_sort.left
  }

#print axioms List.sorted.union_def.helper

theorem List.sorted.union_def [Compare α]: 
  ∀{as bs: List α }, 
  as.sorted ->
  bs.sorted ->
  as.sorted_union bs =
  (as.sorted_merge bs).sorted_difference (as.sorted_intersect bs) := by
  apply List.sorted.induction
  {
    intro bs
    intro _ _
    rw [
      sorted_union.empty_left,
      sorted_merge.empty_left,
      sorted_intersect.empty_left,
      sorted_difference.empty_right,
    ]
  }
  {
    intro a as
    intro _ _
    rw [
      sorted_union.empty_right,
      sorted_merge.empty_right,
      sorted_intersect.empty_right,
      sorted_difference.empty_right,
    ]
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [
      sorted_union.induct_lt a_ord_b,
      sorted_merge.induct_lt a_ord_b,
      sorted_intersect.induct_lt a_ord_b,
    ]
    rw [List.sorted_difference.not_in_right _ _ rfl]
    congr
    apply prev
    exact as_sort.pop
    exact bs_sort
    {
      intro con
      have := List.sorted_intersect.sublist_of_right as (b::bs)
      have := this.containsP con
      have := bs_sort.not_contains a_ord_b
      contradiction
    }
    {
      apply List.sorted_merge.keeps_sorted.helper
      assumption
      apply And.intro
      exact Or.inl a_ord_b
      assumption
      apply List.sorted_merge.keeps_sorted
      exact as_sort.pop
      assumption
    }
    {
      apply List.sorted_intersect.keeps_sorted
      exact as_sort.pop
      exact bs_sort
    }
  }
  {
    intro a as b bs a_ord_b _
    intro as_sort bs_sort
    have a_eq_b := Compare.ord_to_eq a_ord_b
    rw [
      sorted_union.induct_eq a_ord_b,
      sorted_merge.induct_eq a_ord_b,
      sorted_intersect.induct_eq a_ord_b,
      sorted_difference.induct_eq (Compare.ord_id _),
    ]

    have := List.sorted.union_def.helper a [b] (⟨ a_eq_b.symm, True.intro ⟩) as_sort (by
      rw [a_eq_b]
      exact bs_sort)
    rw [List.cons_append, List.cons_append, List.nil_append, List.nil_append] at this
    rw [←this]
    congr
  }
  {
    intro a as b bs a_ord_b prev
    intro as_sort bs_sort
    rw [
      sorted_union.induct_gt a_ord_b,
      sorted_merge.induct_gt a_ord_b,
      sorted_intersect.induct_gt a_ord_b,
    ]
    rw [List.sorted_difference.not_in_right _ _ rfl]
    congr
    apply prev
    exact as_sort
    exact bs_sort.pop
    {
      intro con
      have := List.sorted_intersect.sublist_of_left (a::as) bs
      have := this.containsP con
      have := as_sort.not_contains (Compare.flip a_ord_b)
      contradiction
    }
    {
      apply List.sorted_merge.keeps_sorted.helper
      apply And.intro
      exact Or.inl (Compare.flip a_ord_b)
      assumption
      assumption
      apply List.sorted_merge.keeps_sorted
      assumption
      exact bs_sort.pop
    }
    {
      apply List.sorted_intersect.keeps_sorted
      exact as_sort
      exact bs_sort.pop
    }
  }

#print axioms List.sorted.union_def
