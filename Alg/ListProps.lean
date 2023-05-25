import Alg.Compare

def List.allP (list: List α) (P: α -> Prop) := match list with
  | [] => True
  | x :: xs => P x ∧ xs.allP P

def List.anyP (list: List α) (P: α -> Prop) := match list with
  | [] => False
  | x :: xs => P x ∨ xs.anyP P

def List.containsP (list: List α) (a: α) := list.anyP (fun x => a = x)

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

def List.any_and_all_not {P: α -> Prop} (list: List α)
  (any: list.anyP P)
  (all_not: list.allP (fun x => ¬ P x)):
  False
   := match list with
  | [] => any.elim
  | _::xs => match any with
     | .inl px => all_not.left px
     | .inr pxs => xs.any_and_all_not pxs all_not.right

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

#print axioms List.dec_containsP