import Alg.Compare
import Alg.ListProps

def List.sorted_push [Compare α] (list: List α) (x: α) := match list with
  | [] => [x]
  | a::as => match Compare.dec_le a x with
    | .isTrue _ => a::(as.sorted_push x)
    | .isFalse _ => x::a::as

#print axioms List.sorted_push

def List.sorted_push.keeps_sorted_nonempty [Compare α] (as: List α) (a x: α) (x_le_a: a <= x) : ((a::as).sorted_push x).sorted -> (a::(as.sorted_push x)).sorted := by
  generalize h:sorted (a :: sorted_push as x) = target
  unfold sorted_push
  simp
  cases Compare.dec_le a x
  contradiction
  simp
  intro prev
  rw [h] at prev
  assumption

#print axioms List.sorted_push.keeps_sorted_nonempty

def List.sorted_push.keeps_sorted [Compare α] (list: List α) (x: α) : list.sorted -> (list.sorted_push x).sorted := fun list_sorted => match list with
  | [] => trivial
  | a::as => by
    unfold sorted_push
    cases Compare.dec_le a x with
    | isFalse h => 
    simp
    unfold List.sorted
    apply And.intro
    apply Or.inl
    apply Compare.not_le_is_lt
    assumption
    assumption
    | isTrue h =>
    simp
    match as with
    | [] =>trivial
    | a'::as' =>
    unfold sorted_push
    cases Compare.dec_le a' x with
    | isFalse h => 
    simp only
    unfold sorted
    unfold sorted
    apply And.intro
    assumption
    apply And.intro
    apply Or.inl
    apply Compare.not_le_is_lt
    assumption
    exact list_sorted.right
    | isTrue h =>
    simp
    unfold sorted
    apply And.intro
    exact list_sorted.left
    apply List.sorted_push.keeps_sorted_nonempty
    assumption
    apply List.sorted_push.keeps_sorted
    exact list_sorted.right

#print axioms List.sorted_push.keeps_sorted

def List.sorted_push.keeps_allP [Compare α] (list: List α) (x: α) (P: α -> Prop) : list.allP P -> P x -> (list.sorted_push x).allP P := by
  intro all_list px
  match list with
  | [] =>
    unfold List.sorted_push
    unfold List.allP
    apply And.intro
    exact px
    trivial
  | a::as =>
    unfold List.sorted_push
    unfold List.allP
    cases Compare.dec_le a x <;> simp
    apply And.intro
    exact px
    assumption
    apply And.intro
    exact all_list.left
    apply List.sorted_push.keeps_allP
    exact all_list.right
    assumption

#print axioms List.sorted_push.keeps_allP

def List.sorted_push.keeps_anyP [Compare α] (list: List α) (x: α) (P: α -> Prop) : list.anyP P ∨ P x -> (list.sorted_push x).anyP P := by
  intro all_list_or_px
  match list with
  | [] =>
    match all_list_or_px with
    | .inl _ => contradiction
    | .inr _ =>
    unfold List.sorted_push
    unfold List.anyP
    apply Or.inl
    assumption
  | a::as =>
    unfold List.sorted_push
    unfold List.anyP
    cases Compare.dec_le a x <;> simp
    cases all_list_or_px
    apply Or.inr
    assumption
    apply Or.inl
    assumption
    match all_list_or_px with
    | .inl (.inl _) =>
      apply Or.inl
      assumption
    | .inl (.inr _) =>  
      apply Or.inr
      apply List.sorted_push.keeps_anyP
      apply Or.inl
      assumption
    | .inr _ =>
      apply Or.inr
      apply List.sorted_push.keeps_anyP
      apply Or.inr
      assumption

#print axioms List.sorted_push.keeps_allP

def List.sorted_push.contains [Compare α] (list: List α) (x y: α) : list.containsP y ∨ y = x -> (list.sorted_push x).containsP y := by
  unfold List.containsP
  apply List.sorted_push.keeps_anyP

#print axioms List.sorted_push.contains
