/-
Sorting a list
-/



variable { α : Type } ( f : α → α → Bool) ( r : α → α → Prop)

namespace notes 

/- We sort lists of type α using the 
comparison function f (or r).

If f a₁ a₂ = true, then this is the correct order, 
otherwise it is incorrect.

If r a₁ a₂ has a proof, then this is the correct order, 
otherwise it is incorrect.

What are some examples of sorted lists?

- [] the empty list should be sorted
- for any 'a : α ', then '[a]' is sorted. 
- for any pair of terms 'a₁ a₂ : α ' and any list 'as: List α' such that 
  'f a₁ a₂ = true' and 'a₂ :: as' is sorted, 
  then the list  'a₁ :: a₂ :: as' is also sorted.
- if 'as : List α' that is sorted and 'f a as[0]' then
  a::as is also sorted. 
-/

inductive Sorted (f: α → α →  Bool) : List α → Prop where 
  | nil : Sorted f []  
  | single {a : α } : Sorted f [a]
  | longer {a₁ a₂ : α } {as : List α } (h : f a₁ a₂) 
    (h' : Sorted f (a₂ :: as)) : Sorted f (a₁ :: a₂ :: as)

open Sorted 

example : Sorted (· ≤ ·) [1,2,3] := by
  apply longer 
  · simp 
  · apply longer 
    · simp 
    ·  apply single 

theorem sorted_tail_of_sorted (a : α) (as : List α)
  (h: Sorted f (a::as)) : Sorted f as := by 
  match h with 
  | single => apply nil   
  | longer _  h'' => exact h'' 

def insert (a : α) (l : List α ) : List α :=  
  match l with 
  | [] => [a]
  | a'::as => 
    match f a a' with 
    | true => a::a'::as 
    | false => a':: insert a as 


@[simp]
theorem len_insert_eq_succ_len {a : α} {l : List α} : 
  (insert f a l).length = l.length + 1 := sorry


#check insert

def insertSort (l : List α ) : List α := 
  match l with 
  | [] => [] 
  | a::as => insert f a <| insertSort as

#check insertSort

#eval insertSort (·≤·) [4,5,2,4,5,6]
#eval insertSort (fun (b b' : Bool) => b && b') [true, false, false]
#eval insertSort (fun _ _ => false) [4,5,2,4,5,6]
#eval insertSort (fun _ _ => true) [4,5,2,4,5,6]

class Asymmetric (f : α → α → Bool) where 
  asym {a a'} : !f a a' → f a' a 

open Asymmetric 

def Sorted.cons {a : α} {l : List α} (h₁ : Sorted f l)
  (h₂ : l.length > 0 := by simp) (h₃ : f a l[0]) : Sorted f (a::l) := 
  match h₁ with 
  | nil => single
  | single => longer h₃ single 
  | longer h h' => longer h₃ <| longer h h' 

theorem ordered_of_sorted {a a' : α} (as : List α)
  (h : Sorted f (a::a'::as)) : f a a' := 
  match h with
  | longer h' _ => h'

theorem ordered_cons_insert_of_unordered {a a' : α} {as : List α}
    (h : Sorted f (a'::as)) (h : f a' a) : f a' (insert f a as)[0] := 
  sorry

theorem insert_sorted_of_sorted {a : α} {l : List α} [Asymmetric f] 
    (h : Sorted f l) : Sorted f <| insert f a l := 
  match l with 
  | [] => single   
  | a'::as => 
    match h' : f a a' with 
    | true => by simp [insert, h']; apply longer h' h
    | false => by 
      simp [insert, h']  
      apply cons f
      · apply insert_sorted_of_sorted <| sorted_tail_of_sorted f a' as h
      · apply ordered_cons_insert_of_unordered f h 
        · apply asym; simp; assumption

theorem sorted_of_insertSort (l : List α) [Asymmetric f] : 
    Sorted f <| insertSort f l := 
  match l with
  | [] => nil  
  | a::as => by
    dsimp [insertSort]
    apply insert_sorted_of_sorted f <| sorted_of_insertSort as











