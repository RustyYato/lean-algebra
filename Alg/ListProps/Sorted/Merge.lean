import Alg.ListProps.Sorted

def List.sorted_merge [Compare α] (as bs: List α) := match as with
  | [] => bs
  | a::as' => as'.sorted_merge (bs.sorted_push a)

  def List.sorted_merge.keeps_sorted [Compare α] (as bs: List α) : as.sorted -> bs.sorted -> (as.sorted_merge bs).sorted := by
    intro as_sorted bs_sorted
    match as with
    | [] =>
      unfold List.sorted_merge
      exact bs_sorted
    | a::as' =>
      unfold List.sorted_merge
      apply List.sorted_merge.keeps_sorted
      apply List.sorted.pop
      assumption
      apply List.sorted_push.keeps_sorted
      assumption

#print axioms List.sorted_merge.keeps_sorted

  def List.sorted_merge.keeps_allP {P: α -> Prop} [Compare α] (as bs: List α) : as.allP P -> bs.allP P -> (as.sorted_merge bs).allP P := by
    intro as_all bs_all
    match as with
    | [] =>
      unfold List.sorted_merge
      exact bs_all
    | a::as' =>
      unfold List.sorted_merge
      apply List.sorted_merge.keeps_allP
      exact as_all.right
      apply List.sorted_push.keeps_allP
      assumption
      exact as_all.left

#print axioms List.sorted_merge.keeps_allP

  def List.sorted_merge.keeps_anyP {P: α -> Prop} [Compare α] (as bs: List α) : as.anyP P ∨ bs.anyP P -> (as.sorted_merge bs).anyP P := by
    intro as_any_or_bs_any
    match as with
    | [] =>
      unfold List.sorted_merge
      match as_any_or_bs_any with
      | .inl _ => contradiction
      | .inr h => assumption
    | a::as' =>
      unfold List.sorted_merge
      apply List.sorted_merge.keeps_anyP
      match as_any_or_bs_any with
      | .inl (.inr _) =>
        apply Or.inl
        assumption
      | .inl (.inl _) =>
        apply Or.inr
        apply List.sorted_push.keeps_anyP
        apply Or.inr
        assumption
      | .inr _ =>
        apply Or.inr
        apply List.sorted_push.keeps_anyP
        apply Or.inl
        assumption

#print axioms List.sorted_merge.keeps_anyP

  def List.sorted_merge.contains [Compare α] (as bs: List α) (x: α) : as.containsP x ∨ bs.containsP x -> (as.sorted_merge bs).containsP x := by
    unfold containsP
    apply List.sorted_merge.keeps_anyP

#print axioms List.sorted_merge.contains
