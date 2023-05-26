import Alg.Compare

def List.allP (list: List α) (P: α -> Prop) := match list with
  | [] => True
  | x :: xs => P x ∧ xs.allP P

def List.anyP (list: List α) (P: α -> Prop) := match list with
  | [] => False
  | x :: xs => P x ∨ xs.anyP P

def List.containsP (list: List α) (a: α) := list.anyP (fun x => a = x)

def List.containsP.split {a} {as: List α} : ∀{x}, (a::as).containsP x -> x = a ∨ as.containsP x := id

def List.sorted [Compare α] (list: List α): Prop := match list with
 | [] | [_] => True
 | a :: b :: rest => a <= b ∧ (b::rest).sorted

def List.containsP.pop (as: List α) (a b: α) : as.containsP b -> (a::as).containsP b := by
  intro contains_as
  unfold List.containsP List.anyP
  apply Or.inr
  assumption

def List.sorted.pop [Compare α] (as: List α) (a: α) : (a::as).sorted -> as.sorted := by
  intro aas_sorted
  match as with
  | [] => trivial
  | a'::as' => exact aas_sorted.right

def List.sorted.pop_snd [Compare α] (as: List α) (a b: α) : (a::b::as).sorted -> (a::as).sorted := by
  intro aas_sorted
  match as with
  | [] => trivial
  | a'::as' =>
    apply And.intro
    exact Compare.le_trans aas_sorted.left aas_sorted.right.left
    exact aas_sorted.right.right

def List.any_and_all_not {P: α -> Prop} (list: List α)
  (any: list.anyP P)
  (all_not: list.allP (fun x => ¬ P x)):
  False
   := match list with
  | [] => any.elim
  | _::xs => match any with
     | .inl px => all_not.left px
     | .inr pxs => xs.any_and_all_not pxs all_not.right

def List.allP.and_all_not {P: α -> Prop} {list: List α}
  (all: list.allP P)
  (all_not: list.allP (fun x => ¬ P x)):
  list = []
   := match list with
  | [] => rfl
  | _::_ => (all_not.left all.left).elim

def List.allP.map {P Q: α -> Prop} {list: List α}
  (all: list.allP P): (∀{x}, P x -> Q x) -> list.allP Q
   := fun p_to_q => match list with
  | [] => True.intro
  | _::_ => 
    ⟨ (p_to_q all.left), all.right.map p_to_q ⟩

instance List.dec_containsP [DecidableEq α] (as: List α) (x: α) : Decidable (List.containsP as x) := 
  match as with
  | [] => Decidable.isFalse False.elim
  | a::as' =>
    if h:x = a then Decidable.isTrue (Or.inl h)
    else match List.dec_containsP as' x with
      | .isTrue as'_con => Decidable.isTrue (Or.inr as'_con)
      | .isFalse not_as'_con => Decidable.isFalse (fun x_eq_or_as'_con => match x_eq_or_as'_con with
        | .inl x_eq => h x_eq
        | .inr as'_con => not_as'_con as'_con)

instance List.dec_sorted [Compare α] (as: List α) : Decidable (as.sorted) := 
  match as with
  | [] | [_] => Decidable.isTrue True.intro
  | a::b::xs => by
    apply dec_and
    apply Compare.dec_le
    apply List.dec_sorted

#print axioms List.dec_containsP

def List.sorted.contains [Compare α] {x a: α} : (a::as).sorted -> (a::as).containsP x -> a <= x := by
  intro as_sort as_con
  unfold containsP anyP at as_con
  match as_con with
  | .inl h => 
    rw [h]
    apply Compare.le_id
  | .inr h => 
    match as with
    | [] => contradiction
    | a'::as' =>
    apply Compare.le_trans as_sort.left
    apply as_sort.right.contains
    assumption

def List.sorted.not_contains [Compare α] {x a: α} : List.sorted (a::as) -> x < a -> ¬(a::as).containsP x := by
  intro as_sort x_lt_a as_con
  match as_con.split with
  | .inl h => 
    rw [h] at x_lt_a
    have := Compare.not_lt_id x_lt_a
    contradiction
  | .inr h => 
    match as with
    | [] => contradiction
    | a'::as' =>
    apply (as_sort.pop).not_contains 
    apply Compare.lt_le_trans x_lt_a
    exact as_sort.left
    exact h

def List.subset_of (a b: List α) := ∀x, a.containsP x -> b.containsP x

def List.subset_of.of_empty {as: List α} : as.subset_of [] -> as = [] := by
  intro sub
  match as with
  | [] => rfl
  | x::_ =>
    have := sub x (Or.inl rfl)
    contradiction

#print axioms List.subset_of.of_empty

def List.subset_of.empty {as: List α} : [].subset_of as := by
  intro x con
  contradiction

#print axioms List.subset_of.of_empty

def List.subset_of.pop_left {a: α} {as bs: List α} : (a::as).subset_of bs -> as.subset_of bs := by
  intro sub
  match bs with
  | [] =>
    have := List.subset_of.of_empty sub
    contradiction
  | b::bs' =>
  match as with
  | [] => exact List.subset_of.empty
  | a'::as' =>
  intro x as_cont
  apply sub x
  apply Or.inr
  assumption

#print axioms List.subset_of.pop_left

def List.subset_of.push_left {a: α} {as bs: List α} : bs.containsP a -> as.subset_of bs -> (a::as).subset_of bs := by
  intro conb sub
  intro x cona
  match cona with
  | .inl h => rw [h]; assumption
  | .inr h => exact sub x h

#print axioms List.subset_of.push_left

def List.subset_of.pop_right {b: α} {as bs: List α} : ¬as.containsP b -> as.subset_of (b::bs) -> as.subset_of bs := by
  intro not_con sub
  intro x acon
  match sub x acon with
  | .inr h => assumption
  | .inl h =>
    rw [h] at acon
    contradiction

#print axioms List.subset_of.pop_right

def List.subset_of.push_right {b: α} {as bs: List α}: as.subset_of bs -> as.subset_of (b::bs) := by
  intro sub
  intro x acon
  apply Or.inr
  exact sub x acon

#print axioms List.subset_of.push_right

def List.subset_of.push {x: α} {as bs: List α} : as.subset_of bs -> (x::as).subset_of (x::bs) := by
  intro sub
  intro y cona
  match cona with
  | .inl h => rw [h]; apply Or.inl; rfl
  | .inr h => apply Or.inr; apply sub; assumption

#print axioms List.subset_of.push_left

def List.subset_of.id {as: List α} : as.subset_of as := by
  intro x con
  assumption

#print axioms List.subset_of.of_empty

def List.containsP.allP {as: List α} : ∀{x}, as.containsP x -> as.allP P -> P x := by
  intro x con all
  match as with
  | [] => contradiction
  | a::as' =>
    match con.split with
    | .inl h => rw [h]; exact all.left
    | .inr h => exact h.allP all.right

#print axioms List.containsP.allP

def List.containsP.anyP {as: List α} : ∀{x}, as.containsP x -> P x -> as.anyP P := by
  intro x con px
  match as with
  | [] => contradiction
  | a::as' =>
    match con.split with
    | .inl h => rw [h] at px; exact Or.inl px
    | .inr h => exact Or.inr (h.anyP px)

#print axioms List.containsP.anyP

def List.subset_of.allP {as bs: List α} : as.subset_of bs -> (∀{P}, bs.allP P -> as.allP P) := by
  intro sub P bs_all
  match as with
  | [] => trivial
  | a::as' =>
    apply And.intro
    exact (sub a (Or.inl rfl)).allP bs_all
    apply List.subset_of.allP
    exact sub.pop_left
    assumption

#print axioms List.subset_of.allP

def List.subset_of.anyP {as bs: List α} : as.subset_of bs -> (∀{P}, as.anyP P -> bs.anyP P) := by
  intro sub P bs_any
  match as with
  | [] => contradiction
  | a::as' =>
    match bs_any with
    | .inl h =>
      have conb := sub a (Or.inl rfl)
      exact conb.anyP h
    | .inr h => exact sub.pop_left.anyP h

#print axioms List.subset_of.anyP

def List.subset_of.trans {as bs cs: List α} : as.subset_of bs -> bs.subset_of cs -> as.subset_of cs := by
  intro sub_ab sub_bc
  match as with
  | [] => exact List.subset_of.empty
  | a::as' =>
    apply List.subset_of.push_left
    exact sub_bc a (sub_ab a (Or.inl rfl))
    apply List.subset_of.trans sub_ab.pop_left sub_bc

#print axioms List.subset_of.trans

def List.sublist_of (as bs: List α): Prop := match as with
   | [] => True
   | a::as => match bs with
      |  [] => False
      | b::bs => a = b ∧ as.sublist_of bs ∨ (a::as).sublist_of bs

def List.sublist_of.empty { bs: List α }: [].sublist_of bs := by
  unfold List.sublist_of
  trivial

def List.sublist_of.id { as: List α }: as.sublist_of as := by
  match as with
  | [] => trivial
  | a::as' =>
  apply Or.inl
  apply And.intro
  rfl
  apply List.sublist_of.id

def List.sublist_of.push_right { b: α } { as bs: List α }: as.sublist_of bs -> as.sublist_of (b::bs) := by
  intro sub
  match as with
  | [] => trivial
  | a::as =>
  apply Or.inr
  assumption

def List.sublist_of.pop_left { a: α } { as bs: List α }: (a::as).sublist_of bs -> as.sublist_of bs := by
  intro sub
  match bs with
  | b::bs => 
  match sub with
  | .inl ⟨ _, h ⟩ => exact h.push_right
  | .inr h => exact h.pop_left.push_right

def List.sublist_of.push { x: α } { as bs: List α }: as.sublist_of bs -> (x::as).sublist_of (x::bs) := by
  intro sub
  apply Or.inl
  apply And.intro
  rfl
  assumption

def List.sublist_of.pop { x: α } { as bs: List α }: (x::as).sublist_of (x::bs) -> as.sublist_of bs := by
  intro sub
  match sub with
  | .inl ⟨ _, prf ⟩ => exact prf
  | .inr h => exact h.pop_left

def List.sublist_of.pop_right { b: α } { as bs: List α }: as.sublist_of (b::bs) -> ¬ as.containsP b -> as.sublist_of bs := by
  intro sub not_con
  match as with
  | [] =>
    exact List.sublist_of.empty
  | a::as =>
  match sub with
  | .inl ⟨ a_eq_b, _ ⟩  =>
    rw [a_eq_b] at not_con
    apply False.elim
    apply not_con
    apply Or.inl
    rfl
  | .inr _ =>
    assumption

def List.sublist_of.allP {as bs: List α} : as.sublist_of bs -> (∀{P}, bs.allP P -> as.allP P) := by
  intro sub P all_bs
  match as with
  | [] => trivial
  | a::as =>
  match bs with
  | b::bs =>
    match sub with
    | .inl ⟨ h, rest ⟩ =>
      apply And.intro
      rw [h]
      exact all_bs.left
      apply List.sublist_of.allP
      exact rest
      exact all_bs.right
    | .inr rest =>
      apply List.sublist_of.allP
      exact rest
      exact all_bs.right
